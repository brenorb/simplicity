(** The actual post-memset wNAF phase for scalars below 2^255.
    Zeroed output cells and initial temporaries are premises at this internal
    boundary. The original external memset, entry/freeing and negative branch
    are not discharged here. No whole-function or public jet is registered. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_exec C.jet_sx_mem C.jet_sx_exec C.jet_struct_copy_loads
  C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_fns
  C.jet_secp_curve_statements C.jet_secp_wnaf_digit C.jet_secp_wnaf_control
  C.jet_secp_wnaf_loop C.jet_secp_scalar_get_bits C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition wnaf_scalar_copy := nth 9 wnaf_statements Sskip.
Definition wnaf_sign_select := nth 10 wnaf_statements Sskip.
Definition wnaf_post_memset := statement_sequence (skipn 9 wnaf_statements)
  (snd (split_statement_last (fn_body f_secp256k1_ecmult_wnaf))).
Lemma wnaf_scalar_copy_source : wnaf_scalar_copy=
  Sassign (Evar _s (Tstruct __5826 noattr))
    (Ederef (Etempvar _a (tptr (Tstruct __5826 noattr))) (Tstruct __5826 noattr)).
Proof. reflexivity. Qed.
Lemma wnaf_post_memset_source : wnaf_post_memset=
  Ssequence wnaf_scalar_copy (Ssequence wnaf_sign_select wnaf_loop_return).
Proof. reflexivity. Qed.

Theorem exec_wnaf_scalar_copy le m n ba abase bs :
  le!_a=Some (Vptr ba (Ptrofs.repr abase)) -> ba<>bs ->
  scalar_at m ba abase (map Int64.repr (scalar_limbs_of n)) ->
  Mem.range_perm m bs 0 32 Cur Writable ->
  exists mc,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_scalar_copy E0 le mc Out_normal /\
    scalar_at mc bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    Mem.nextblock mc=Mem.nextblock m /\
    (forall bx pos k p, Mem.perm mc bx pos k p <-> Mem.perm m bx pos k p) /\
    lframe (fun bx _=>bx<>bs) m mc.
Proof.
  intros HA Separate [Length [Base [Align [Max [ReadableRange Loads]]]]] WritableRange.
  assert (AU : Ptrofs.unsigned (Ptrofs.repr abase)=abase) by (apply Ptrofs.unsigned_repr;lia).
  destruct (Mem.range_perm_loadbytes m ba abase 32 ReadableRange) as (bytes & Read).
  pose proof (Mem.loadbytes_length _ _ _ _ _ Read) as Size.
  assert (Space : Mem.range_perm m bs 0 (0+Z.of_nat (length bytes)) Cur Writable)
    by (rewrite Size;exact WritableRange).
  destruct (Mem.range_perm_storebytes m bs 0 bytes Space) as (mc & Store).
  assert (Copied : Mem.loadbytes mc bs 0 32=Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as H;rewrite Size in H;exact H. }
  exists mc;split.
  - rewrite wnaf_scalar_copy_source.
    eapply exec_Sassign_copy with (b:=bs) (b':=ba) (ofs:=Ptrofs.zero)
      (ofs':=Ptrofs.repr abase) (v:=Vptr ba (Ptrofs.repr abase)).
    + apply eval_Evar_local;reflexivity.
    + eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact HA|].
      apply deref_loc_copy;reflexivity.
    + reflexivity.
    + eapply assign_loc_copy with (b':=ba) (ofs':=Ptrofs.repr abase) (bytes:=bytes).
      * reflexivity.
      * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr abase));rewrite AU;exact Align.
      * intros _;change (8|0);exists 0;reflexivity.
      * left;congruence.
      * change (Mem.loadbytes m ba (Ptrofs.unsigned (Ptrofs.repr abase)) 32=Some bytes).
        rewrite AU;exact Read.
      * exact Store.
  - split.
    + unfold scalar_at;split;[exact Length|];split;[lia|];split;[exists 0;reflexivity|];split.
      * change Ptrofs.max_unsigned with 18446744073709551615;lia.
      * split.
        -- intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|].
           eapply Mem.perm_implies;[apply WritableRange;exact Range|constructor].
        -- intros i limb Nth.
           assert (Index : (i<4)%nat).
           { rewrite <-Length;apply nth_error_Some;rewrite Nth;discriminate. }
           eapply equal_loadbytes_field with (m1:=m) (b1:=ba) (base1:=abase) (n:=32) (bytes:=bytes).
           ++ pose proof (Nat2Z.is_nonneg i);lia.
           ++ change (8*Z.of_nat i+8<=32);lia.
           ++ exact Read.
           ++ exact Copied.
           ++ change (8|0+8*Z.of_nat i);exists (Z.of_nat i);ring.
           ++ apply Loads;exact Nth.
    + split;[eapply Mem.nextblock_storebytes;exact Store|];split.
      * intros;split;intro P;[eapply Mem.perm_storebytes_2|eapply Mem.perm_storebytes_1];eassumption.
      * apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
        intros pos Range NE;apply NE;reflexivity.
Qed.

Definition wnaf_top_call := match wnaf_sign_select with Ssequence call _=>call | _=>Sskip end.
Definition wnaf_negative_branch := match wnaf_sign_select with
  Ssequence _ (Sifthenelse _ negative _)=>negative | _=>Sskip end.
Definition wnaf_small_temps le := PTree.set _t'1 (Vint Int.zero) le.
Lemma wnaf_top_call_source : wnaf_top_call=
  curve_call _secp256k1_scalar_get_bits f_secp256k1_scalar_get_bits (Some _t'1)
    [Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
      Econst_int (Int.repr 255) tint;Econst_int Int.one tint].
Proof. reflexivity. Qed.
Lemma wnaf_sign_select_source : wnaf_sign_select=Ssequence wnaf_top_call
  (Sifthenelse (Etempvar _t'1 tuint) wnaf_negative_branch Sskip).
Proof. reflexivity. Qed.

Theorem exec_wnaf_sign_small le m n bs :
  0<=n<2^255 -> scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_sign_select E0 (wnaf_small_temps le) m Out_normal.
Proof.
  intros N Storage.
  assert (Power : 2^255<=2^256) by (apply Z.pow_le_mono_r;lia).
  assert (Zero : (n/2^255) mod 2=0) by (rewrite Z.div_small by lia;reflexivity).
  rewrite wnaf_sign_select_source;unfold wnaf_small_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint Int.zero) le).
  - rewrite wnaf_top_call_source.
    eapply exec_curve_call with
      (vargs:=[Vptr bs Ptrofs.zero;Vint (Int.repr 255);Vint Int.one]) (v:=Vint Int.zero).
    + unfold secp_pure;repeat (first [left;reflexivity|right]).
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      * reflexivity.
      * eapply eval_Econs;[constructor|reflexivity|].
        eapply eval_Econs;[constructor|reflexivity|constructor].
    + pose proof (eval_scalar_get_bits_slice m bs 0 n 255 1 ltac:(lia) ltac:(lia)
        ltac:(lia) ltac:(cbn;lia) Storage) as Call.
      change (2^1) with 2 in Call;rewrite Zero in Call;exact Call.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
      [apply eval_Etempvar;apply PTree.gss|reflexivity|constructor].
Qed.

Lemma wnaf_small_fields le bit len w carry sign b base last :
  wnaf_loop_fields le bit len w carry sign b base last ->
  wnaf_loop_fields (wnaf_small_temps le) bit len w carry sign b base last.
Proof.
  intros (HB & HL & HW & HC & HS & HP & HT);unfold wnaf_loop_fields,wnaf_small_temps;
    repeat split;rewrite PTree.gso by discriminate;assumption.
Qed.

Theorem exec_wnaf_post_memset_small le m n len w ba abase bs b base :
  0<=n<2^255 -> 0<=len<=256 -> 2<=w<=31 ->
  le!_a=Some (Vptr ba (Ptrofs.repr abase)) ->
  wnaf_loop_fields le 0 len w 0 1 b base (-1) ->
  scalar_at m ba abase (map Int64.repr (scalar_limbs_of n)) -> ba<>bs -> b<>bs ->
  Mem.range_perm m bs 0 32 Cur Writable ->
  0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  (forall i, 0<=i<len -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
  (forall i, 0<=i<len -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
  exists lef mf carry last digits,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_post_memset E0 lef mf
      (Out_return (Some (Vint (Int.repr (last+1)),tint))) /\
    wnaf_loop_fields lef len len w carry 1 b base last /\
    (carry=0 \/ carry=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base len w 1 len last digits /\
    wnaf_weighted digits (Z.to_nat len)+2^len*(n/2^len+carry)=n /\
    0<=last+1<=len /\ Mem.nextblock mf=Mem.nextblock m /\
    (forall bx pos k p, Mem.perm mf bx pos k p <-> Mem.perm m bx pos k p) /\
    lframe (fun bx _=>bx<>bs /\ bx<>b) m mf /\
    (n<2^(len-1) -> carry=0 /\ wnaf_weighted digits (Z.to_nat len)=n).
Proof.
  intros N Len W HA Fields Storage SourceSeparate OutputSeparate LocalWritable Base Max Access Load.
  destruct (exec_wnaf_scalar_copy le m n ba abase bs HA SourceSeparate Storage LocalWritable)
    as (mc & Copy & StorageC & BlocksC & PermC & FrameC).
  assert (AccessC : forall i, 0<=i<len -> Mem.valid_access mc Mint32 b (base+4*i) Writable).
  { intros i Range;destruct (Access i Range) as [Cells Align];split;[|exact Align].
    intros pos R;apply (proj2 (PermC b pos Cur Writable));apply Cells;exact R. }
  assert (LoadC : forall i, 0<=i<len -> Mem.load Mint32 mc b (base+4*i)=Some (Vint Int.zero)).
  { intros i Range;rewrite (proj1 FrameC Mint32 b (base+4*i)).
    - apply Load;exact Range.
    - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
        [apply Access;exact Range|constructor].
    - intros pos R;exact OutputSeparate. }
  assert (Select : Clight2.exec_stmt secp_ge (wnaf_env bs) le mc wnaf_sign_select E0
    (wnaf_small_temps le) mc Out_normal) by (apply exec_wnaf_sign_small with (n:=n);assumption).
  assert (Power : 2^255<=2^256) by (apply Z.pow_le_mono_r;lia).
  destruct (exec_wnaf_loop_zero (wnaf_small_temps le) mc n len w 1 b base bs
    ltac:(lia) Len W (or_introl eq_refl) (wnaf_small_fields _ _ _ _ _ _ _ _ _ Fields)
    StorageC OutputSeparate Base Max AccessC LoadC)
    as (lef & mf & carry & last & digits & Loop & Final & Carry & StorageF & ArrayF & Value &
      ReturnBound & Effect & Reconstruction).
  destruct Effect as [BlocksF [PermF FrameF]].
  exists lef,mf,carry,last,digits;split.
  - rewrite wnaf_post_memset_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Select|exact Loop].
  - split;[exact Final|];split;[exact Carry|];split;[exact StorageF|];split;[exact ArrayF|];split;[exact Value|].
    split;[exact ReturnBound|];split;[congruence|];split.
    + intros bx pos k p;rewrite <-PermF;apply PermC.
    + split;[|exact Reconstruction].
      eapply lframe_trans.
      * eapply lframe_implies;[exact FrameC|intros bx pos [NEs NEb] VB;exact NEs].
      * eapply lframe_implies;[exact FrameF|intros bx pos [NEs NEb] VB;exact NEb].
Qed.
