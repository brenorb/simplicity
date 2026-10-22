(** Execution of the original wNAF loop and return, after caller initialization.
    The weighted equation retains the final residual and carry; neither is
    assumed zero. The initial zero loads must still be established by the
    actual caller. This is not a whole-function or public jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition wnaf_update (digits : Z -> Z) bit digit :=
  fun i => if zeq i bit then digit else digits i.
Fixpoint wnaf_weighted (digits : Z -> Z) (count : nat) : Z :=
  match count with
  | O => 0
  | S k => wnaf_weighted digits k + digits (Z.of_nat k)*2^(Z.of_nat k)
  end.
Lemma wnaf_weighted_ext count a b :
  (forall i, 0<=i<Z.of_nat count -> a i=b i) ->
  wnaf_weighted a count=wnaf_weighted b count.
Proof.
  induction count as [|k IH];intro H;[reflexivity|].
  cbn [wnaf_weighted];rewrite IH by (intros;apply H;rewrite Nat2Z.inj_succ;lia).
  rewrite H by (rewrite Nat2Z.inj_succ;pose proof (Nat2Z.is_nonneg k);lia);reflexivity.
Qed.
Lemma wnaf_weighted_update count digits bit digit :
  0<=bit<Z.of_nat count ->
  wnaf_weighted (wnaf_update digits bit digit) count =
    wnaf_weighted digits count+(digit-digits bit)*2^bit.
Proof.
  induction count as [|k IH];intro Bit;[cbn in Bit;lia|].
  cbn [wnaf_weighted];unfold wnaf_update at 2;destruct (zeq (Z.of_nat k) bit) as [Same|Other].
  - subst bit.
    assert (Prefix : wnaf_weighted (wnaf_update digits (Z.of_nat k) digit) k=wnaf_weighted digits k).
    { apply wnaf_weighted_ext;intros i Range;unfold wnaf_update;destruct zeq;[lia|reflexivity]. }
    rewrite Prefix;ring.
  - rewrite IH by (rewrite Nat2Z.inj_succ in Bit;lia);ring.
Qed.

Definition wnaf_small_digit w digit :=
  digit=0 \/ (digit mod 2=1 /\ -2^(w-1)<digit<2^(w-1)).
Definition wnaf_last digits bit last : Prop :=
  -1<=last<bit /\
  (forall i, 0<=i<bit -> digits i<>0 -> i<=last) /\
  (last= -1 \/ digits last<>0).
Record wnaf_array_state (m : mem) b base len w sign bit last (digits : Z->Z) : Prop := {
  wnaf_array_access : forall i, 0<=i<len -> Mem.valid_access m Mint32 b (base+4*i) Writable;
  wnaf_array_load : forall i, 0<=i<len ->
    Mem.load Mint32 m b (base+4*i)=Some (Vint (Int.repr (sign*digits i)));
  wnaf_array_suffix : forall i, bit<=i<len -> digits i=0;
  wnaf_array_digits : forall i, 0<=i<len -> wnaf_small_digit w (digits i);
  wnaf_array_last : wnaf_last digits bit last
}.

Lemma wnaf_array_skip m b base len w sign bit bit' last digits :
  0<=bit -> bit<bit'<=len ->
  wnaf_array_state m b base len w sign bit last digits ->
  wnaf_array_state m b base len w sign bit' last digits.
Proof.
  intros Bit Advance [Access Load Suffix Digits [Last [Highest Present]]];constructor;try assumption.
  - intros i Range;apply Suffix;lia.
  - split;[lia|];split;[|exact Present].
    intros i Range Nonzero;destruct (zlt i bit);[apply Highest;[lia|exact Nonzero]|].
    rewrite Suffix in Nonzero by lia;contradiction.
Qed.

Lemma wnaf_array_store m mf b base len w sign bit bit' last digits digit :
  0<=bit -> bit<bit'<=len -> digit mod 2=1 -> -2^(w-1)<digit<2^(w-1) ->
  Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (sign*digit)))=Some mf ->
  wnaf_array_state m b base len w sign bit last digits ->
  wnaf_array_state mf b base len w sign bit' bit (wnaf_update digits bit digit).
Proof.
  intros Bit Advance Odd Bounds Store [Access Load Suffix Digits Last];constructor.
  - intros i Range;eapply Mem.store_valid_access_1;[exact Store|apply Access;exact Range].
  - intros i Range;unfold wnaf_update;destruct (zeq i bit) as [->|Other].
    + rewrite (Mem.load_store_same _ _ _ _ _ _ Store);reflexivity.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ Store);[apply Load;exact Range|].
      right;change (base+4*i+4<=base+4*bit \/ base+4*bit+4<=base+4*i);lia.
  - intros i Range;unfold wnaf_update;destruct zeq;[lia|apply Suffix;lia].
  - intros i Range;unfold wnaf_update;destruct zeq;[right;split;assumption|apply Digits;exact Range].
  - split;[lia|];split.
    + intros i Range Nonzero;unfold wnaf_update in Nonzero;destruct zeq;[lia|].
      destruct (zle i bit);[assumption|];rewrite Suffix in Nonzero by lia;contradiction.
    + right;unfold wnaf_update;destruct zeq;[intro Zero;rewrite Zero in Odd;discriminate|congruence].
Qed.

Definition wnaf_memory_effect b m mf : Prop :=
  Mem.nextblock mf=Mem.nextblock m /\
  (forall bx pos k p, Mem.perm m bx pos k p <-> Mem.perm mf bx pos k p) /\
  lframe (fun bx _=>bx<>b) m mf.
Lemma wnaf_memory_refl b m : wnaf_memory_effect b m m.
Proof. split;[reflexivity|];split;[intros;tauto|apply lframe_refl]. Qed.
Lemma wnaf_memory_store m mf b ofs v : Mem.store Mint32 m b ofs v=Some mf ->
  wnaf_memory_effect b m mf.
Proof.
  intro Store;split;[eapply Mem.nextblock_store;exact Store|];split.
  - intros;split;intro P;[eapply Mem.perm_store_1|eapply Mem.perm_store_2];eassumption.
  - apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
    intros pos Range NE;apply NE;reflexivity.
Qed.
Lemma wnaf_memory_trans b m mi mf : wnaf_memory_effect b m mi ->
  wnaf_memory_effect b mi mf -> wnaf_memory_effect b m mf.
Proof.
  intros [Blocks1 [Perm1 Frame1]] [Blocks2 [Perm2 Frame2]];split;[congruence|];split.
  - intros;rewrite Perm1,Perm2;reflexivity.
  - eapply lframe_trans;eassumption.
Qed.

Lemma eval_wnaf_loop_guard e le m bit len :
  0<=bit<=len -> len<=256 ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_len=Some (Vint (Int.repr len)) ->
  eval_expr secp_ge e le m (Ebinop Olt (Etempvar _bit tint) (Etempvar _len tint) tint)
    (Vint (if Z.ltb bit len then Int.one else Int.zero)).
Proof.
  intros Bit Len HB HL;eapply eval_Ebinop;
    [apply eval_Etempvar;exact HB|apply eval_Etempvar;exact HL|].
  change (Some (Val.of_bool (Int.lt (Int.repr bit) (Int.repr len)))=
    Some (Vint (if Z.ltb bit len then Int.one else Int.zero))).
  unfold Int.lt;rewrite !Int.signed_repr by
    (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
  destruct (zlt bit len),(Z.ltb_spec bit len);try lia;reflexivity.
Qed.

Lemma wnaf_weighted_step count digits digits' n bit bit' carry carry' digit target :
  0<=bit<=bit' ->
  wnaf_weighted digits' count=wnaf_weighted digits count+digit*2^bit ->
  n/2^bit+carry=digit+2^(bit'-bit)*(n/2^bit'+carry') ->
  wnaf_weighted digits count+2^bit*(n/2^bit+carry)=target ->
  wnaf_weighted digits' count+2^bit'*(n/2^bit'+carry')=target.
Proof.
  intros Bit Sum Step Weighted.
  assert (Power : 2^bit'=2^bit*2^(bit'-bit)).
  { replace bit' with (bit+(bit'-bit)) at 1 by lia;rewrite Z.pow_add_r by lia;reflexivity. }
  rewrite Sum,<-Weighted,Step.
  rewrite Power at 1.
  ring.
Qed.

Theorem exec_wnaf_array_step le m n bit len w carry sign b base bs last digits target :
  0<=n<2^256 -> 0<=bit<len -> len<=256 -> 2<=w<=31 ->
  (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le bit len w carry sign b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  wnaf_array_state m b base len w sign bit last digits ->
  wnaf_weighted digits (Z.to_nat len)+2^bit*(n/2^bit+carry)=target ->
  exists le' mf bit' carry' last' digits' out,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 le' mf out /\
    wnaf_loop_fields le' bit' len w carry' sign b base last' /\
    bit<bit'<=len /\ (carry'=0 \/ carry'=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base len w sign bit' last' digits' /\
    wnaf_weighted digits' (Z.to_nat len)+2^bit'*(n/2^bit'+carry')=target /\
    wnaf_memory_effect b m mf /\ out_normal_or_continue out.
Proof.
  intros N Bit Len W Carry Sign Fields Storage Separate Base Max Array Weighted.
  pose proof (wnaf_array_last _ _ _ _ _ _ _ _ _ Array) as Last.
  destruct Last as [Last _].
  destruct (exec_wnaf_loop_body_step le m n bit len w carry sign b base bs last
    N Bit Len W Last Carry Sign Fields Storage Separate Base ltac:(lia)
    (wnaf_array_access _ _ _ _ _ _ _ _ _ Array bit Bit))
    as (le' & mf & bit' & carry' & digit & last' & out & Exec & Fields' & Advance & Last' &
      Carry' & Storage' & Out & Value & Effect).
  assert (Normal : out_normal_or_continue out) by (destruct Out as [-> | ->];constructor).
  destruct Effect as [(Zero & Same & LastSame)|(Odd & Bounds & Store & LastSame)].
  - subst digit mf last'.
    exists le',m,bit',carry',last,digits,out.
    split;[exact Exec|];split;[exact Fields'|];split;[exact Advance|];split;[exact Carry'|].
    split;[exact Storage'|];split.
    + eapply wnaf_array_skip with (bit:=bit);[lia|exact Advance|exact Array].
    + split.
      * eapply wnaf_weighted_step with (bit:=bit) (carry:=carry) (digit:=0);
          [lia| |exact Value|exact Weighted];ring.
      * split;[apply wnaf_memory_refl|exact Normal].
  - subst last'.
    exists le',mf,bit',carry',bit,(wnaf_update digits bit digit),out.
    split;[exact Exec|];split;[exact Fields'|];split;[exact Advance|];split;[exact Carry'|].
    split;[exact Storage'|];split.
    + eapply wnaf_array_store with (last:=last);
        [lia|exact Advance|exact Odd|exact Bounds|exact Store|exact Array].
    + split.
      * eapply wnaf_weighted_step with (bit:=bit) (carry:=carry) (digit:=digit);
          [lia| |exact Value|exact Weighted].
        rewrite wnaf_weighted_update by (rewrite Z2Nat.id by lia;exact Bit).
        rewrite (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array bit ltac:(lia));ring.
      * split;[eapply wnaf_memory_store;exact Store|exact Normal].
Qed.

Theorem exec_wnaf_loop_bounded fuel : forall le m n bit len w carry sign b base bs last digits target,
  len-bit<=Z.of_nat fuel ->
  0<=n<2^256 -> 0<=bit<=len -> len<=256 -> 2<=w<=31 ->
  (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le bit len w carry sign b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  wnaf_array_state m b base len w sign bit last digits ->
  wnaf_weighted digits (Z.to_nat len)+2^bit*(n/2^bit+carry)=target ->
  exists lef mf carryf lastf digitsf,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop E0 lef mf Out_normal /\
    wnaf_loop_fields lef len len w carryf sign b base lastf /\
    (carryf=0 \/ carryf=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base len w sign len lastf digitsf /\
    wnaf_weighted digitsf (Z.to_nat len)+2^len*(n/2^len+carryf)=target /\
    wnaf_memory_effect b m mf.
Proof.
  induction fuel as [|fuel IH];intros le m n bit len w carry sign b base bs last digits target
    Fuel N Bit Len W Carry Sign Fields Storage Separate Base Max Array Weighted;
    destruct (zeq bit len) as [Done|More].
  all:try (subst bit;exists le,m,carry,last,digits;split;
    [rewrite wnaf_loop_body_source;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor];
      eapply exec_Sseq_2;[|discriminate];
      eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
      [pose proof (eval_wnaf_loop_guard (wnaf_env bs) le m len len ltac:(lia) Len
        (proj1 Fields) (proj1 (proj2 Fields))) as Guard;
        rewrite Z.ltb_irrefl in Guard;exact Guard|reflexivity|constructor]
    |split;[exact Fields|];split;[exact Carry|];split;[exact Storage|];split;[exact Array|];
      split;[exact Weighted|apply wnaf_memory_refl]]).
  - cbn in Fuel;lia.
  - assert (Before : 0<=bit<len) by lia.
    destruct (exec_wnaf_array_step le m n bit len w carry sign b base bs last digits target
      N Before Len W Carry Sign Fields Storage Separate Base Max Array Weighted)
      as (lei & mi & biti & carryi & lasti & digitsi & out & Body & FieldsI & Advance &
        CarryI & StorageI & ArrayI & WeightedI & EffectI & Normal).
    destruct (IH lei mi n biti len w carryi sign b base bs lasti digitsi target
      ltac:(rewrite Nat2Z.inj_succ in Fuel;lia) N ltac:(lia) Len W CarryI Sign FieldsI
      StorageI Separate Base Max ArrayI WeightedI)
      as (lef & mf & carryf & lastf & digitsf & Rest & FieldsF & CarryF & StorageF &
        ArrayF & WeightedF & EffectF).
    exists lef,mf,carryf,lastf,digitsf;split.
    + rewrite wnaf_loop_body_source in Rest |- *.
      eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
        (le1:=lei) (m1:=mi) (out1:=out) (le2:=lei) (m2:=mi).
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
        -- eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
           pose proof (eval_wnaf_loop_guard (wnaf_env bs) le m bit len Bit Len
             (proj1 Fields) (proj1 (proj2 Fields))) as Guard.
           rewrite (proj2 (Z.ltb_lt bit len) ltac:(lia)) in Guard;exact Guard.
        -- exact Body.
      * exact Normal.
      * constructor.
      * exact Rest.
    + split;[exact FieldsF|];split;[exact CarryF|];split;[exact StorageF|];split;[exact ArrayF|].
      split;[exact WeightedF|];eapply wnaf_memory_trans;eassumption.
Qed.

Theorem exec_wnaf_loop le m n bit len w carry sign b base bs last digits target :
  0<=n<2^256 -> 0<=bit<=len -> len<=256 -> 2<=w<=31 ->
  (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le bit len w carry sign b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  wnaf_array_state m b base len w sign bit last digits ->
  wnaf_weighted digits (Z.to_nat len)+2^bit*(n/2^bit+carry)=target ->
  exists lef mf carryf lastf digitsf,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop E0 lef mf Out_normal /\
    wnaf_loop_fields lef len len w carryf sign b base lastf /\
    (carryf=0 \/ carryf=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base len w sign len lastf digitsf /\
    wnaf_weighted digitsf (Z.to_nat len)+2^len*(n/2^len+carryf)=target /\
    wnaf_memory_effect b m mf.
Proof.
  intros N Bit Len W Carry Sign Fields Storage Separate Base Max Array Weighted.
  eapply exec_wnaf_loop_bounded with (fuel:=Z.to_nat (len-bit));try eassumption.
  rewrite Z2Nat.id by lia;lia.
Qed.

Definition wnaf_loop_return := Ssequence wnaf_loop
  (snd (C.jet_secp_statement_prefix.split_statement_last (fn_body f_secp256k1_ecmult_wnaf))).
Lemma wnaf_return_source :
  snd (C.jet_secp_statement_prefix.split_statement_last (fn_body f_secp256k1_ecmult_wnaf))=
  Sreturn (Some (Ebinop Oadd (Etempvar _last_set_bit tint) (Econst_int Int.one tint) tint)).
Proof. reflexivity. Qed.
Lemma exec_wnaf_return e le m last : -1<=last<256 ->
  le!_last_set_bit=Some (Vint (Int.repr last)) ->
  Clight2.exec_stmt secp_ge e le m
    (snd (C.jet_secp_statement_prefix.split_statement_last (fn_body f_secp256k1_ecmult_wnaf))) E0
    le m (Out_return (Some (Vint (Int.repr (last+1)),tint))).
Proof.
  intros Last HT;rewrite wnaf_return_source;apply exec_Sreturn_some;eapply eval_Ebinop;
    [apply eval_Etempvar;exact HT|constructor|].
  change (Some (Vint (Int.add (Int.repr last) Int.one))=Some (Vint (Int.repr (last+1)))).
  change Int.one with (Int.repr 1);rewrite Int.add_signed,!Int.signed_repr by
    (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
Qed.

Lemma wnaf_weighted_zero count : wnaf_weighted (fun _=>0) count=0.
Proof. induction count;[reflexivity|cbn [wnaf_weighted];rewrite IHcount;ring]. Qed.
Lemma wnaf_array_zero m b base len w sign : 0<=len ->
  (forall i, 0<=i<len -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
  (forall i, 0<=i<len -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
  wnaf_array_state m b base len w sign 0 (-1) (fun _=>0).
Proof.
  intros Len Access Load;constructor.
  - exact Access.
  - intros i Range;rewrite Z.mul_0_r;apply Load;exact Range.
  - intros;reflexivity.
  - intros;left;reflexivity.
  - split;[lia|];split;[intros;lia|left;reflexivity].
Qed.

Theorem exec_wnaf_loop_zero le m n len w sign b base bs :
  0<=n<2^256 -> 0<=len<=256 -> 2<=w<=31 -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le 0 len w 0 sign b base (-1) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  (forall i, 0<=i<len -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
  (forall i, 0<=i<len -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
  exists lef mf carry last digits,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_return E0 lef mf
      (Out_return (Some (Vint (Int.repr (last+1)),tint))) /\
    wnaf_loop_fields lef len len w carry sign b base last /\
    (carry=0 \/ carry=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base len w sign len last digits /\
    wnaf_weighted digits (Z.to_nat len)+2^len*(n/2^len+carry)=n /\
    0<=last+1<=len /\ wnaf_memory_effect b m mf.
Proof.
  intros N Len W Sign Fields Storage Separate Base Max Access Load.
  assert (Array : wnaf_array_state m b base len w sign 0 (-1) (fun _=>0))
    by (apply wnaf_array_zero;try assumption;lia).
  assert (Weighted : wnaf_weighted (fun _=>0) (Z.to_nat len)+2^0*(n/2^0+0)=n).
  { rewrite wnaf_weighted_zero;change (2^0) with 1;rewrite Z.div_1_r;ring. }
  destruct (exec_wnaf_loop le m n 0 len w 0 sign b base bs (-1) (fun _=>0) n
    N ltac:(lia) ltac:(lia) W (or_introl eq_refl) Sign Fields Storage Separate Base Max Array Weighted)
    as (lef & mf & carry & last & digits & Exec & Final & Carry & StorageF & ArrayF & Value & Effect).
  pose proof (wnaf_array_last _ _ _ _ _ _ _ _ _ ArrayF) as [Last _].
  exists lef,mf,carry,last,digits;split.
  - unfold wnaf_loop_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Exec|].
    apply exec_wnaf_return;[lia|].
    destruct Final as (_ & _ & _ & _ & _ & _ & HT);exact HT.
  - split;[exact Final|];split;[exact Carry|];split;[exact StorageF|];split;[exact ArrayF|].
    split;[exact Value|];split;[lia|exact Effect].
Qed.
