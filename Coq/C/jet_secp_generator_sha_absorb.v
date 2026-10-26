(** The two original prefix/key call pairs in generator_generate_internal.
    Derive the readonly prefixes from the actual initializer and retain their
    state through the calls. Finalization and digest serialization follow later. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_secp_linkage C.jet_secp_statement_prefix
  C.jet_secp_generator_sha_start C.jet_secp_sha_startup C.jet_secp_sha_absorb_short
  C.jet_clight_internal_preserve.
Require C.jets_sha.
Require Import C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_sha_prefix_id (second:bool) := if second then _prefix2 else _prefix1.
Definition generator_sha_prefix_var (second:bool) := if second then v_prefix2 else v_prefix1.
Definition generator_sha_prefix_block second := secp_symbol_block (generator_sha_prefix_id second).
Definition generator_sha_prefix_bytes (second:bool) : list int :=
  map Int.repr ((if second then [50;110;100] else [49;115;116])++[32;103;101;110;101;114;97;116;105;111;110;58;32]).
Definition generator_sha_prefix_state second m :=
  (forall i,(i<16)%nat ->Mem.load Mint8unsigned m (generator_sha_prefix_block second) (Z.of_nat i)=
    Some (Vint (nth i (generator_sha_prefix_bytes second) Int.zero))) /\
  (forall pos,~Mem.perm m (generator_sha_prefix_block second) pos Max Writable).
Lemma generator_sha_prefix_length second : length (generator_sha_prefix_bytes second)=16%nat.
Proof. destruct second;reflexivity. Qed.
Lemma generator_sha_prefix_symbol second : Genv.find_symbol secp_ge (generator_sha_prefix_id second)=
  Some (generator_sha_prefix_block second).
Proof. destruct second;vm_compute;reflexivity. Qed.
Lemma generator_sha_prefix_info second : Genv.find_var_info (Genv.globalenv jets_secp.prog)
  (generator_sha_prefix_block second)=Some (generator_sha_prefix_var second).
Proof. destruct second;vm_compute;reflexivity. Qed.
Lemma generator_sha_uchars_symbol : Genv.find_symbol secp_ge _sha256_uchars=
  Some (secp_symbol_block _sha256_uchars).
Proof. vm_compute;reflexivity. Qed.
Lemma generator_sha_uchars_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block _sha256_uchars) Ptrofs.zero)=Some (Internal f_sha256_uchars).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge generator_sha_prefix_block.

Theorem generator_sha_prefix_initial second m : Genv.init_mem jets_secp.prog=Some m ->
  generator_sha_prefix_state second m.
Proof.
  intro Init;destruct (Genv.init_mem_characterization jets_secp.prog _ (generator_sha_prefix_info second) Init)
    as (_ & Bounds & Loads & _).
  specialize (Loads ltac:(destruct second;reflexivity));split.
  - intros i Index;destruct second;do 16 (destruct i as [|i];[cbn in Loads;tauto|]);lia.
  - intros pos Perm;pose proof (proj2 (Bounds pos Max Writable Perm)) as Order.
    destruct second;change (perm_order Readable Writable) in Order;inversion Order.
Qed.
Lemma generator_sha_prefix_preserved second m mf : generator_sha_prefix_state second m ->
  readonly_preserved m mf ->generator_sha_prefix_state second mf.
Proof.
  intros [Bytes NoWrite] [Forward Unchanged].
  assert (Valid:Mem.valid_block m (generator_sha_prefix_block second)).
  { pose proof (Bytes 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  split.
  - intros i Index;eapply Mem.load_unchanged_on;[exact Unchanged| |apply Bytes;exact Index].
    intros ofs Range;split;[exact Valid|apply NoWrite].
  - intros pos Perm;apply (NoWrite pos);exact (proj2 (Forward _ Valid) pos Writable Perm).
Qed.
Lemma generator_sha_prefix_separate second m bx : generator_sha_prefix_state second m ->
  Mem.range_perm m bx 0 88 Cur Freeable ->bx<>generator_sha_prefix_block second.
Proof.
  intros [_ NoWrite] Owned Same;subst bx;apply (NoWrite 0);apply Mem.perm_cur_max;
    eapply Mem.perm_implies;[apply Owned;lia|constructor].
Qed.

Definition generator_sha_absorb_call second (key:bool) :=
  Scall None (Evar _sha256_uchars (type_of_function f_sha256_uchars))
    [Eaddrof (Evar (generator_sha_context_id second) generator_sha_ctx_type) (tptr generator_sha_ctx_type);
     if key then Etempvar _key32 (tptr tuchar) else Evar (generator_sha_prefix_id second) (tarray tuchar 17);
     Econst_int (Int.repr (if key then 32 else 16)) tint].
Definition generator_sha_absorb second :=
  statement_sequence [generator_sha_absorb_call second false;generator_sha_absorb_call second true] Sskip.
Definition generator_sha_final_calls (second:bool) := match nth (if second then 11%nat else 7%nat)
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip with
  | Ssequence _ (Ssequence _ (Ssequence _ rest))=>rest | _=>Sskip end.
Lemma generator_sha_absorb_source (second:bool) : nth (if second then 11%nat else 7%nat)
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip=
  Ssequence (generator_sha_start second)
    (statement_sequence [generator_sha_absorb_call second false;generator_sha_absorb_call second true]
      (generator_sha_final_calls second)).
Proof. destruct second;reflexivity. Qed.

Lemma exec_generator_sha_absorb_call second (key:bool) e le m mf bc ba oa (bytes:list int) :
  e!_sha256_uchars=None ->e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!(generator_sha_prefix_id second)=None ->le!_key32=Some (Vptr ba oa) ->
  length bytes=(if key then 32%nat else 16%nat) ->
  Clight2.eval_funcall secp_ge m (Internal f_sha256_uchars)
    [Vptr bc Ptrofs.zero;
     if key then Vptr ba oa else Vptr (generator_sha_prefix_block second) Ptrofs.zero;
     Vlong (Int64.repr (Z.of_nat (length bytes)))] E0 mf (Vint Int.one) ->
  Clight2.exec_stmt secp_ge e le m (generator_sha_absorb_call second key) E0 le mf Out_normal.
Proof.
  intros Fun Context Prefix Key Length Call;change le with (set_opttemp None (Vint Int.one) le) at 2.
  unfold generator_sha_absorb_call;eapply exec_Scall with
    (vf:=Vptr (secp_symbol_block _sha256_uchars) Ptrofs.zero) (f:=Internal f_sha256_uchars)
    (vargs:=[Vptr bc Ptrofs.zero;
      if key then Vptr ba oa else Vptr (generator_sha_prefix_block second) Ptrofs.zero;
      Vlong (Int64.repr (Z.of_nat (length bytes)))]) (vres:=Vint Int.one).
  - reflexivity.
  - eapply eval_Elvalue;[apply eval_Evar_global;[exact Fun|exact generator_sha_uchars_symbol]|].
    apply deref_loc_reference;reflexivity.
  - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|].
    eapply eval_Econs with (v1:=if key then Vptr ba oa else Vptr (generator_sha_prefix_block second) Ptrofs.zero).
    + destruct key.
      * apply eval_Etempvar;exact Key.
      * eapply eval_Elvalue;[apply eval_Evar_global;[exact Prefix|apply generator_sha_prefix_symbol]|].
        apply deref_loc_reference;reflexivity.
    + destruct key;reflexivity.
    + eapply eval_Econs;[apply eval_Econst_int| |constructor];rewrite Length;destruct key;reflexivity.
  - exact generator_sha_uchars_funct.
  - reflexivity.
  - exact Call.
Qed.

Theorem exec_generator_sha_absorb_owned (Hmodel:memcpy_model) second key e le m bc ba oa out :
  e!_sha256_uchars=None ->e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!(generator_sha_prefix_id second)=None ->le!_key32=Some (Vptr ba oa) ->
  bc<>ba ->length key=32%nat ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  generator_sha_prefix_state second m ->secp_sha_startup m ->Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.load Mptr m bc 0=Some out ->Mem.load Mint64 m bc 8=Some (Vlong Int64.zero) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=Some (Vint (nth i key Int.zero))) ->
  exists mf,Clight2.exec_stmt secp_ge e le m (generator_sha_absorb second) E0 le mf Out_normal /\
  Mem.load Mptr mf bc 0=Some out /\Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 48)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  (forall i,(i<48)%nat ->Mem.load Mint8unsigned mf bc (16+Z.of_nat i)=
    Some (Vint (nth i (generator_sha_prefix_bytes second++key) Int.zero))) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\lframe (fun b _=>b<>bc) m mf /\
  readonly_preserved m mf /\secp_sha_startup mf /\generator_sha_prefix_state second mf.
Proof.
  intros Fun Context Prefix Key Separate Length SourceHi PrefixState Startup Owned Pointer Counter Overflow Bytes.
  pose proof (generator_sha_prefix_length second) as PL.
  destruct (eval_secp_sha_absorb_short Hmodel [] (generator_sha_prefix_bytes second) m bc
    (generator_sha_prefix_block second) Ptrofs.zero out ltac:(cbn [length];lia)
    (generator_sha_prefix_separate second m bc PrefixState Owned) Startup Owned
    ltac:(rewrite PL;change (16<=18446744073709551615);lia) Pointer Counter Overflow
    ltac:(intros i Index;cbn in Index;lia) ltac:(intros i Index;apply (proj1 PrefixState);rewrite PL in Index;exact Index))
    as (mi & First & PointerI & CounterI & OverflowI & BufferI & OwnedI & FrameI & ReadonlyI & StartupI).
  cbn [app] in CounterI,BufferI.
  assert (KeyValid:Mem.valid_block m ba).
  { pose proof (Bytes 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  destruct (eval_secp_sha_absorb_short Hmodel (generator_sha_prefix_bytes second) key mi bc ba oa out
    ltac:(rewrite PL,Length;lia) Separate StartupI OwnedI ltac:(rewrite Length;exact SourceHi)
    PointerI CounterI OverflowI BufferI)
    as (mf & Second & PointerF & CounterF & OverflowF & BufferF & OwnedF & FrameF & ReadonlyF & StartupF).
  { intros i Index;rewrite (proj1 FrameI) by (first [exact KeyValid|intros;congruence]);apply Bytes;rewrite Length in Index;exact Index. }
  exists mf;split.
  - unfold generator_sha_absorb;cbn [statement_sequence];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
    + eapply exec_generator_sha_absorb_call with (key:=false) (ba:=ba) (oa:=oa) (bytes:=generator_sha_prefix_bytes second);
        [exact Fun|exact Context|exact Prefix|exact Key|exact PL|exact First].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|constructor].
      eapply exec_generator_sha_absorb_call with (key:=true) (bytes:=key);
        [exact Fun|exact Context|exact Prefix|exact Key|exact Length|exact Second].
  - split;[exact PointerF|];split.
    + rewrite app_length,PL,Length in CounterF;exact CounterF.
    + split;[exact OverflowF|];split.
      * intros i Index;apply BufferF;rewrite app_length,PL,Length;exact Index.
      * split;[exact OwnedF|];split;[eapply lframe_trans;eassumption|];split.
        -- eapply preserved_trans;eassumption.
        -- split;[exact StartupF|];eapply generator_sha_prefix_preserved;[|exact ReadonlyF].
           eapply generator_sha_prefix_preserved;[exact PrefixState|exact ReadonlyI].
Qed.
