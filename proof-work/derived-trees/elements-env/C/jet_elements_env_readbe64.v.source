(** Execution of [ReadBE64(b)] (sha256.h) in the Elements environment unit:
    the eight bytes at [b] are returned as one big-endian 64-bit word.
    elements/env.c reads every explicit amount of the raw transaction with
    it ([copyRawAmt]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_ReadBE64_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _ReadBE64 = Some (sha_symbol_block _ReadBE64).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_ReadBE64_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _ReadBE64) Ptrofs.zero) =
    Some (Internal f_ReadBE64).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

(** One byte of the C expression: [(uint_fast64_t)(b[i] & 0xff) << s]. *)
Definition be64_part (x : int) (s : Z) : int64 :=
  Int64.shl' (Int64.repr (Int.signed (Int.and x (Int.repr 255)))) (Int.repr s).

Definition c_be64 (x1 x2 x3 x4 x5 x6 x7 x8 : int) : int64 :=
  Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or (Int64.or
    (be64_part x1 56) (be64_part x2 48)) (be64_part x3 40)) (be64_part x4 32))
    (be64_part x5 24)) (be64_part x6 16)) (be64_part x7 8))
    (Int64.repr (Int.signed (Int.and x8 (Int.repr 255)))).

Definition be64_le (b : block) (o : ptrofs) (x1 x2 x3 x4 x5 x6 x7 x8 : int) : temp_env :=
  PTree.set _t'8 (Vint x8) (PTree.set _t'7 (Vint x7) (PTree.set _t'6 (Vint x6) (PTree.set _t'5 (Vint x5)
  (PTree.set _t'4 (Vint x4) (PTree.set _t'3 (Vint x3) (PTree.set _t'2 (Vint x2) (PTree.set _t'1 (Vint x1)
    (PTree.set _b (Vptr b o) (create_undef_temps (fn_temps f_ReadBE64)))))))))).

Lemma eval_sha_ReadBE64 m b o x1 x2 x3 x4 x5 x6 x7 x8 :
  Ptrofs.unsigned o + 7 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o) = Some (Vint x1) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 1) = Some (Vint x2) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 2) = Some (Vint x3) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 3) = Some (Vint x4) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 4) = Some (Vint x5) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 5) = Some (Vint x6) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 6) = Some (Vint x7) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o + 7) = Some (Vint x8) ->
  Clight2.eval_funcall sha_ge m (Internal f_ReadBE64) [Vptr b o] E0 m
    (Vlong (c_be64 x1 x2 x3 x4 x5 x6 x7 x8)).
Proof.
  intros HM L1 L2 L3 L4 L5 L6 L7 L8.
  assert (Hload : forall i x le, 0 <= i <= 7 -> le!_b = Some (Vptr b o) ->
    Mem.load Mint8unsigned m b (Ptrofs.unsigned o + i) = Some (Vint x) ->
    eval_expr sha_ge empty_env le m
      (Ederef (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Econst_int (Int.repr i) tint) (tptr tuchar)) tuchar)
      (Vint x)).
  { intros i x le Hi Hb HL. eapply eval_Elvalue.
    - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Hb|apply eval_Econst_int|reflexivity].
    - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
      rewrite ptr_byte_offset by lia. exact HL. }
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m)
    (le2 := be64_le b o x1 x2 x3 x4 x5 x6 x7 x8)
    (out := Out_return (Some (Vlong (c_be64 x1 x2 x3 x4 x5 x6 x7 x8), tulong))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - cbn [f_ReadBE64 fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 0); [lia|reflexivity|]. rewrite Z.add_0_r. exact L1. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 1); [lia|reflexivity|exact L2]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 2); [lia|reflexivity|exact L3]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 3); [lia|reflexivity|exact L4]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 4); [lia|reflexivity|exact L5]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 5); [lia|reflexivity|exact L6]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 6); [lia|reflexivity|exact L7]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    { apply exec_Sset. apply (Hload 7); [lia|reflexivity|exact L8]. }
    apply exec_Sreturn_some. unfold c_be64, be64_part, be64_le.
    be32_ev.
  - cbn; split; [discriminate|reflexivity].
  - reflexivity.
Qed.

(** On byte values the C expression is the arithmetic big-endian word. *)
Definition be64_value (x1 x2 x3 x4 x5 x6 x7 x8 : Z) : Z :=
  ((((((x1 * 256 + x2) * 256 + x3) * 256 + x4) * 256 + x5) * 256 + x6) * 256 + x7) * 256 + x8.

Lemma byte_and_255 x : 0 <= Int.unsigned x < 256 -> Int.and x (Int.repr 255) = x.
Proof.
  intros Hx. unfold Int.and. rewrite (Int.unsigned_repr 255) by (change Int.max_unsigned with 4294967295; lia).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_small by lia. apply Int.repr_unsigned.
Qed.

Lemma byte_signed x : 0 <= Int.unsigned x < 256 -> Int.signed x = Int.unsigned x.
Proof.
  intros Hx. unfold Int.signed.
  destruct (zlt (Int.unsigned x) Int.half_modulus) as [_|HH];
    [reflexivity|change Int.half_modulus with 2147483648 in HH; lia].
Qed.

Lemma be64_part_repr x s : 0 <= Int.unsigned x < 256 -> 0 <= s <= 56 ->
  be64_part x s = Int64.repr (Int.unsigned x * 2 ^ s).
Proof.
  intros Hx Hs. unfold be64_part. rewrite byte_and_255, byte_signed by exact Hx.
  unfold Int64.shl'.
  rewrite (Int64.unsigned_repr (Int.unsigned x))
    by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite (Int.unsigned_repr s) by (change Int.max_unsigned with 4294967295; lia).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma or64_disjoint acc lo k hi : 0 <= k < 64 -> acc = hi * 2 ^ k -> 0 <= lo < 2 ^ k -> 0 <= hi ->
  acc + lo < 2 ^ 64 ->
  Int64.or (Int64.repr acc) (Int64.repr lo) = Int64.repr (acc + lo).
Proof.
  intros Hk -> Hlo Hhi Hb.
  assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  unfold Int64.or. rewrite !Int64.unsigned_repr
    by (change Int64.max_unsigned with (2 ^ 64 - 1); nia).
  f_equal. rewrite <- Z.shiftl_mul_pow2 by lia.
  assert (HL : Z.land (Z.shiftl hi k) lo = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n k) as [Hlt|Hge].
    - rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec lo 0) as [->|Hne]; [rewrite Z.bits_0; apply andb_false_r|].
      rewrite (Z.bits_above_log2 lo n); [apply andb_false_r|lia|].
      assert (H0 : 0 < lo) by lia. pose proof (proj1 (Z.log2_lt_pow2 lo k H0) (proj2 Hlo)). lia. }
  rewrite (Z.add_nocarry_lxor _ _ HL), (Z.lxor_lor _ _ HL). reflexivity.
Qed.

Lemma c_be64_value x1 x2 x3 x4 x5 x6 x7 x8 :
  0 <= Int.unsigned x1 < 256 -> 0 <= Int.unsigned x2 < 256 -> 0 <= Int.unsigned x3 < 256 ->
  0 <= Int.unsigned x4 < 256 -> 0 <= Int.unsigned x5 < 256 -> 0 <= Int.unsigned x6 < 256 ->
  0 <= Int.unsigned x7 < 256 -> 0 <= Int.unsigned x8 < 256 ->
  c_be64 x1 x2 x3 x4 x5 x6 x7 x8 =
    Int64.repr (be64_value (Int.unsigned x1) (Int.unsigned x2) (Int.unsigned x3) (Int.unsigned x4)
                           (Int.unsigned x5) (Int.unsigned x6) (Int.unsigned x7) (Int.unsigned x8)).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8.
  unfold c_be64. rewrite byte_and_255, byte_signed by exact H8. rewrite !be64_part_repr by lia.
  set (a1 := Int.unsigned x1) in *. set (a2 := Int.unsigned x2) in *. set (a3 := Int.unsigned x3) in *.
  set (a4 := Int.unsigned x4) in *. set (a5 := Int.unsigned x5) in *. set (a6 := Int.unsigned x6) in *.
  set (a7 := Int.unsigned x7) in *. set (a8 := Int.unsigned x8) in *.
  simpl Z.pow.
  Local Ltac orstep k hi :=
    match goal with
    | |- context [Int64.or (Int64.repr ?acc) (Int64.repr ?lo)] =>
        rewrite (or64_disjoint acc lo k hi) by (simpl Z.pow; lia)
    end.
  orstep 56 a1.
  orstep 48 (a1 * 256 + a2).
  orstep 40 ((a1 * 256 + a2) * 256 + a3).
  orstep 32 (((a1 * 256 + a2) * 256 + a3) * 256 + a4).
  orstep 24 ((((a1 * 256 + a2) * 256 + a3) * 256 + a4) * 256 + a5).
  orstep 16 (((((a1 * 256 + a2) * 256 + a3) * 256 + a4) * 256 + a5) * 256 + a6).
  orstep 8 ((((((a1 * 256 + a2) * 256 + a3) * 256 + a4) * 256 + a5) * 256 + a6) * 256 + a7).
  f_equal. unfold be64_value. lia.
Qed.
