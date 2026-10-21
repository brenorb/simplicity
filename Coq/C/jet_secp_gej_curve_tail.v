(** Last four actual projective-checker calls: in-place square, times seven,
    field addition and equality.  No weak normalization occurs in this C path. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_square_inplace_storage C.jet_secp_field_mul7 C.jet_secp_field_add_scaled
  C.jet_secp_equal_loose C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Theorem gej_curve_tail_calls y2 x3 z3 m b_y bx bz :
  (forall i, (i<5)%nat -> Int64.unsigned (y2 i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i<5)%nat -> Int64.unsigned (x3 i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  square_input_bounds z3 -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m b_y 0 (words5 y2) -> fe_at m bx 0 (words5 x3) -> fe_at m bz 0 (words5 z3) ->
  Mem.range_perm m b_y 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m6 m7 m8 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m6 Vundef /\
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul_int)
    [Vptr bz Ptrofs.zero;Vint (Int.repr 7)] E0 m7 Vundef /\
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_add)
    [Vptr bx Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m8 Vundef /\
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf
    (Vint (if Z.eqb (radix_value y2 mod feP)
      ((radix_value x3+7*(radix_value z3*radix_value z3)) mod feP) then Int.one else Int.zero)) /\
  Mem.range_perm mf b_y 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  Mem.range_perm mf bz 0 40 Cur Freeable /\
  lframe (fun b _ => b<>b_y /\ b<>bx /\ b<>bz) m mf.
Proof.
  intros BY BX BZ HYX HYZ HXZ HY HX HZ HFY HFX HFZ.
  destruct (eval_square_inplace_from_storage z3 m bz BZ HZ HFZ)
    as (m6 & C6 & Z6 & ZF6 & V6 & B6 & BT6 & E6).
  pose proof (field_at_lframe m m6 b_y 0 _ _ HY E6 ltac:(intro pos;congruence)) as Y6.
  pose proof (field_at_lframe m m6 bx 0 _ _ HX E6 ltac:(intro pos;congruence)) as X6.
  pose proof (curve_keep_free _ m m6 b_y 40 ltac:(lia) HFY E6 ltac:(intro pos;congruence)) as YF6.
  pose proof (curve_keep_free _ m m6 bx 40 ltac:(lia) HFX E6 ltac:(intro pos;congruence)) as XF6.
  destruct (eval_field_mul7_from_storage (square_words z3) m6 bz
    ltac:(intros i HI;exact (proj2 (BT6 i HI))) Z6 ZF6)
    as (m7 & C7 & Z7 & ZF7 & V7 & B7 & E7).
  pose proof (field_at_lframe m6 m7 b_y 0 _ _ Y6 E7 ltac:(intro pos;congruence)) as Y7.
  pose proof (field_at_lframe m6 m7 bx 0 _ _ X6 E7 ltac:(intro pos;congruence)) as X7.
  pose proof (curve_keep_free _ m6 m7 b_y 40 ltac:(lia) YF6 E7 ltac:(intro pos;congruence)) as YF7.
  pose proof (curve_keep_free _ m6 m7 bx 40 ltac:(lia) XF6 E7 ltac:(intro pos;congruence)) as XF7.
  destruct (eval_field_add_scaled x3 (mul7_words (square_words z3)) m7 bx bz BX B7 HXZ X7 Z7 XF7 ZF7)
    as (m8 & C8 & X8 & XF8 & ZF8 & V8 & B8 & E8).
  pose proof (field_at_lframe m7 m8 b_y 0 _ _ Y7 E8 ltac:(intro pos;split;congruence)) as Y8.
  pose proof (curve_keep_free _ m7 m8 b_y 40 ltac:(lia) YF7 E8 ltac:(intro pos;split;congruence)) as YF8.
  destruct (eval_field_equal_loose_owned y2 (field_sum_words x3 (mul7_words (square_words z3)))
    m8 b_y bx HYX BY B8 Y8 X8 YF8 XF8) as (mf & C9 & YF9 & XF9 & E9).
  pose proof (curve_keep_free _ m8 mf bz 40 ltac:(lia) ZF8 E9 ltac:(intro pos;split;congruence)) as ZF9.
  assert (HRight : radix_value (field_sum_words x3 (mul7_words (square_words z3))) mod feP=
    (radix_value x3+7*(radix_value z3*radix_value z3)) mod feP).
  { rewrite V8,V7. change (radix_value (square_words z3) mod feP=
      (radix_value z3*radix_value z3) mod feP) in V6.
    rewrite (Z.add_mod (radix_value x3) (7*radix_value (square_words z3)) feP),
      (Z.add_mod (radix_value x3) (7*(radix_value z3*radix_value z3)) feP),
      (Z.mul_mod 7 (radix_value (square_words z3)) feP),
      (Z.mul_mod 7 (radix_value z3*radix_value z3) feP),V6
      by (unfold feP,feR;lia);reflexivity. }
  rewrite HRight in C9.
  exists m6,m7,m8,mf;split;[exact C6|]. split;[exact C7|]. split;[exact C8|]. split;[exact C9|].
  split;[exact YF9|]. split;[exact XF9|]. split;[exact ZF9|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact E6|]. intros b pos (_ & _ & HN) HV;exact HN.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact E7|]. intros b pos (_ & _ & HN) HV;exact HN.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact E8|]. intros b pos (_ & NX & NZ) HV;split;assumption.
      * eapply lframe_implies;[exact E9|]. intros b pos (NY & NX & _) HV;split;assumption.
Qed.
