(** Execution of [ReadBE32] in the SHA translation unit: four byte loads
    assembled into a big-endian 32-bit word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_ctx8_model.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma sha_ReadBE32_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _ReadBE32 = Some (sha_symbol_block _ReadBE32).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_ReadBE32_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _ReadBE32) Ptrofs.zero) =
    Some (Internal f_ReadBE32).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Definition c_be32 (x1 x2 x3 x4 : int) : int :=
  Int.or (Int.or (Int.or (Int.shl x1 (Int.repr 24))
    (Int.shl (Int.and x2 (Int.repr 255)) (Int.repr 16)))
    (Int.shl (Int.and x3 (Int.repr 255)) (Int.repr 8)))
    (Int.and x4 (Int.repr 255)).

Lemma ptr_byte_offset (o : ptrofs) (i : Z) :
  0 <= i <= 1000 -> Ptrofs.unsigned o + i <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr i)))) =
    Ptrofs.unsigned o + i.
Proof.
  intros Hi Hm. pose proof (Ptrofs.unsigned_range o) as HO.
  assert (HI : Ptrofs.of_ints (Int.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_ints. rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia. }
  rewrite HI, Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr i) by
    (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
  apply Ptrofs.unsigned_repr. lia.
Qed.

Ltac be32_ev :=
  first [apply eval_Etempvar; reflexivity | apply eval_Econst_int
        | eapply eval_Ebinop; [be32_ev|be32_ev|reflexivity]
        | eapply eval_Ecast; [be32_ev|reflexivity]].

Definition be32_le (b : block) (o : ptrofs) (x1 x2 x3 x4 : int) : temp_env :=
  PTree.set _t'4 (Vint x4) (PTree.set _t'3 (Vint x3) (PTree.set _t'2 (Vint x2) (PTree.set _t'1 (Vint x1)
    (PTree.set _b (Vptr b o) (create_undef_temps (fn_temps f_ReadBE32)))))).

Lemma eval_sha_ReadBE32 m b o x1 x2 x3 x4 :
  Ptrofs.unsigned o + 3 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o) = Some (Vint x1) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 1) = Some (Vint x2) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 2) = Some (Vint x3) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 3) = Some (Vint x4) ->
  Clight2.eval_funcall sha_ge m (Internal f_ReadBE32) [Vptr b o] E0 m (Vint (c_be32 x1 x2 x3 x4)).
Proof.
  intros HM L1 L2 L3 L4.
  assert (Hload : forall i x le, 0 <= i <= 3 -> le!_b = Some (Vptr b o) ->
    Mem.load Mint8unsigned m b (Ptrofs.unsigned o + i) = Some (Vint x) ->
    eval_expr sha_ge empty_env le m
      (Ederef (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Econst_int (Int.repr i) tint) (tptr tuchar)) tuchar)
      (Vint x)).
  { intros i x le Hi Hb HL. eapply eval_Elvalue.
    - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Hb|apply eval_Econst_int|reflexivity].
    - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
      rewrite ptr_byte_offset by lia. exact HL. }
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m)
    (le2 := be32_le b o x1 x2 x3 x4) (out := Out_return (Some (Vint (c_be32 x1 x2 x3 x4), tuint))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - cbn [f_ReadBE32 fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 0); [lia|reflexivity|]. rewrite Z.add_0_r. exact L1. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 1); [lia|reflexivity|exact L2]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 2); [lia|reflexivity|exact L3]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 3); [lia|reflexivity|exact L4]. }
    apply exec_Sreturn_some. unfold c_be32, be32_le.
    be32_ev.
  - cbn; split; [discriminate|reflexivity].
  - reflexivity.
Qed.

(** The C expression is the arithmetic big-endian word on byte values. *)
Lemma lor_shift8 hi lo : 0 <= hi -> 0 <= lo < 256 -> Z.lor (Z.shiftl hi 8) lo = hi * 256 + lo.
Proof.
  intros Hhi Hlo.
  assert (HL : Z.land (Z.shiftl hi 8) lo = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n 8) as [Hs|Hs].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - assert (HF : Z.testbit lo n = false).
      { destruct (Z.eq_dec lo 0) as [->|Hz]; [apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|].
        assert (Z.log2 lo < 8) by (apply Z.log2_lt_pow2; [lia|change (2 ^ 8) with 256; lia]). lia. }
      rewrite HF. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact HL. rewrite <- Z.add_nocarry_lxor by exact HL.
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma byte_and_255 x : Int.unsigned x < 256 -> Int.and x (Int.repr 255) = x.
Proof.
  intros H. change (Int.repr 255) with (Int.repr (two_p 8 - 1)).
  rewrite <- Int.zero_ext_and by lia.
  apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
  destruct (zlt i 8) as [Hs|Hs]; [reflexivity|].
  symmetry. apply Int.bits_size_2. 
  assert (HS : Int.size x <= 8).
  { apply Int.bits_size_3; [lia|]. intros j Hj.
    unfold Int.testbit. pose proof (Int.unsigned_range x) as HR.
    destruct (Z.eq_dec (Int.unsigned x) 0) as [->|Hz]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    assert (Z.log2 (Int.unsigned x) < 8) by (apply Z.log2_lt_pow2; [lia|change (2 ^ 8) with 256; lia]). lia. }
  lia.
Qed.

Lemma c_be32_be32 x1 x2 x3 x4 :
  Int.unsigned x1 < 256 -> Int.unsigned x2 < 256 -> Int.unsigned x3 < 256 -> Int.unsigned x4 < 256 ->
  c_be32 x1 x2 x3 x4 = be32 x1 x2 x3 x4.
Proof.
  intros H1 H2 H3 H4. unfold c_be32, be32.
  rewrite !byte_and_255 by assumption.
  pose proof (Int.unsigned_range x1) as R1. pose proof (Int.unsigned_range x2) as R2.
  pose proof (Int.unsigned_range x3) as R3. pose proof (Int.unsigned_range x4) as R4.
  set (u1 := Int.unsigned x1) in *. set (u2 := Int.unsigned x2) in *.
  set (u3 := Int.unsigned x3) in *. set (u4 := Int.unsigned x4) in *.
  assert (S1 : Int.shl x1 (Int.repr 24) = Int.repr (Z.shiftl u1 24)) by reflexivity.
  assert (S2 : Int.shl x2 (Int.repr 16) = Int.repr (Z.shiftl u2 16)) by reflexivity.
  assert (S3 : Int.shl x3 (Int.repr 8) = Int.repr (Z.shiftl u3 8)) by reflexivity.
  rewrite S1, S2, S3. unfold Int.or.
  assert (E1 : Z.shiftl u1 24 = u1 * 16777216) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (E2 : Z.shiftl u2 16 = u2 * 65536) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (E3 : Z.shiftl u3 8 = u3 * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  assert (MU : Int.max_unsigned = 4294967295) by reflexivity.
  rewrite (Int.unsigned_repr (Z.shiftl u1 24)) by lia.
  rewrite (Int.unsigned_repr (Z.shiftl u2 16)) by lia.
  rewrite (Int.unsigned_repr (Z.shiftl u3 8)) by lia.
  assert (A : Z.lor (Z.shiftl u1 24) (Z.shiftl u2 16) = (u1 * 256 + u2) * 65536).
  { replace (Z.shiftl u1 24) with (Z.shiftl (Z.shiftl u1 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
    rewrite <- Z.shiftl_lor, lor_shift8 by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  rewrite A. rewrite (Int.unsigned_repr ((u1 * 256 + u2) * 65536)) by lia.
  assert (B : Z.lor ((u1 * 256 + u2) * 65536) (Z.shiftl u3 8) = ((u1 * 256 + u2) * 256 + u3) * 256).
  { replace ((u1 * 256 + u2) * 65536) with (Z.shiftl (Z.shiftl (u1 * 256 + u2) 8) 8)
      by (rewrite Z.shiftl_shiftl by lia; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    rewrite <- Z.shiftl_lor, lor_shift8 by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  rewrite B. rewrite (Int.unsigned_repr (((u1 * 256 + u2) * 256 + u3) * 256)) by lia.
  replace (((u1 * 256 + u2) * 256 + u3) * 256) with (Z.shiftl ((u1 * 256 + u2) * 256 + u3) 8)
    by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  rewrite lor_shift8 by lia. f_equal. lia.
Qed.

Lemma load_byte_range m b ofs x :
  Mem.load Mint8unsigned m b ofs = Some (Vint x) -> Int.unsigned x < 256.
Proof.
  intros HL. pose proof (Mem.load_cast _ _ _ _ _ HL) as HC. cbn in HC.
  injection HC as HC. rewrite HC.
  pose proof (Int.zero_ext_range 8 x ltac:(change Int.zwordsize with 32; lia)) as HR.
  change (two_p 8) with 256 in HR. lia.
Qed.

Lemma be_words_length (n : nat) : forall bs, length bs = (4 * n)%nat -> length (be_words bs) = n.
Proof.
  induction n; intros bs HL.
  - destruct bs; [reflexivity|discriminate].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in HL; try lia.
    cbn [be_words length]. f_equal. apply IHn. lia.
Qed.

Lemma be_words_nth (i : nat) : forall bs, (4 * i + 3 < length bs)%nat ->
  nth i (be_words bs) Int.zero =
    be32 (nth (4 * i) bs Int.zero) (nth (4 * i + 1) bs Int.zero)
         (nth (4 * i + 2) bs Int.zero) (nth (4 * i + 3) bs Int.zero).
Proof.
  induction i; intros bs HL.
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in HL; try lia. reflexivity.
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; cbn [length] in HL; try lia.
    cbn [be_words]. change (nth (S i) (be32 b0 b1 b2 b3 :: be_words rest) Int.zero) with
      (nth i (be_words rest) Int.zero).
    rewrite IHi by lia.
    replace (4 * S i)%nat with (S (S (S (S (4 * i))))) by lia. reflexivity.
Qed.
