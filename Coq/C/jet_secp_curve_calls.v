(** The first three actual arithmetic calls of ge_is_valid_var, in C order.
    No intermediate memory, call execution or desired result is a premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_numeric C.jet_secp_square_columns C.jet_secp_square_separate_numeric.
Require Import C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric.
Require Import C.jet_secp_field_read_preservation.
Require Import C.jet_secp_curve_square C.jet_secp_curve_square_caller C.jet_secp_curve_mul C.jet_secp_curve_frame.
Require Import C.jet_secp_curve_tail.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Theorem curve_square_cube_calls x y m ba b_y2 bx :
  square_input_bounds x -> square_input_bounds y ->
  ba<>b_y2 -> ba<>bx -> b_y2<>bx ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b_y2 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  exists m1 m2 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y2 Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b_y2 0 (words5 (square_words y)) /\
  fe_at mf bx 0 (words5 (point_mul_words (square_words x) x)) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf b_y2 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  radix_value (square_words y) mod feP = (radix_value y * radix_value y) mod feP /\
  radix_value (point_mul_words (square_words x) x) mod feP =
    (radix_value x * radix_value x * radix_value x) mod feP /\
  (forall i, (i < 5)%nat -> Int64.unsigned (square_words y i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  (forall i, (i < 5)%nat -> Int64.unsigned (point_mul_words (square_words x) x i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (fun b _ => b<>ba /\ b<>b_y2 /\ b<>bx) m mf.
Proof.
  intros BX BY HAY HAX HYX HX HY HFA HFY HFX.
  destruct (eval_curve_square_from_storage true y m b_y2 ba BY HFY HY HFA (not_eq_sym HAY))
    as (m1 & C1 & Y1 & YF1 & A1Y & AF1 & VY & BY1 & F1).
  pose proof (curve_frame_two (curve_square_regs true) b_y2 ba m m1 eq_refl F1) as E1.
  pose proof (curve_square_other_field true (words5 x) m m1 b_y2 ba
    (not_eq_sym HAY) HX eq_refl F1) as A1X.
  pose proof (curve_keep_free _ m m1 bx 40 ltac:(lia) HFX E1
    ltac:(intro pos; split; congruence)) as XF1.
  destruct (eval_curve_square_from_storage false x m1 bx ba BX XF1 A1X AF1 (not_eq_sym HAX))
    as (m2 & C2 & X2 & XF2 & A2X & AF2 & VX & BX2 & F2).
  pose proof (curve_frame_two (curve_square_regs false) bx ba m1 m2 eq_refl F2) as E2.
  pose proof (field_at_lframe m1 m2 b_y2 0 (words5 (square_words y)) _ Y1 E2
    ltac:(intro pos; split; congruence)) as Y2.
  pose proof (curve_keep_free _ m1 m2 b_y2 40 ltac:(lia) YF1 E2
    ltac:(intro pos; split; congruence)) as YF2.
  pose proof (curve_square_other_field false (words5 y) m1 m2 bx ba
    (not_eq_sym HAX) A1Y eq_refl F2) as A2Y.
  destruct (eval_curve_mul_numeric (square_words x) x m2 bx ba
    (field_operand_from_bounds _ (square_result_reusable x BX))
    (field_operand_from_bounds x BX) (not_eq_sym HAX) X2 XF2 A2X AF2)
    as (mf & C3 & X3 & XF3 & A3X & AF3 & VC & BC & F3).
  pose proof (curve_frame_two curve_mul_regs bx ba m2 mf eq_refl F3) as E3.
  pose proof (field_at_lframe m2 mf b_y2 0 (words5 (square_words y)) _ Y2 E3
    ltac:(intro pos; split; congruence)) as Y3.
  pose proof (curve_keep_free _ m2 mf b_y2 40 ltac:(lia) YF2 E3
    ltac:(intro pos; split; congruence)) as YF3.
  pose proof (curve_mul_other_field (words5 y) m2 mf bx ba (not_eq_sym HAX) A2Y eq_refl F3) as A3Y.
  change (radix_value (square_words x) mod feP = (radix_value x * radix_value x) mod feP) in VX.
  assert (HCube : radix_value (point_mul_words (square_words x) x) mod feP =
    (radix_value x * radix_value x * radix_value x) mod feP).
  { rewrite VC, Z.mul_mod by (unfold feP, feR; lia).
    rewrite VX. rewrite <- Z.mul_mod by (unfold feP, feR; lia). reflexivity. }
  exists m1,m2,mf.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [exact Y3|]. split; [exact X3|]. split; [exact A3X|]. split; [exact A3Y|].
  split; [exact AF3|]. split; [exact YF3|]. split; [exact XF3|].
  split; [exact VY|]. split; [exact HCube|].
  split; [intros i HI; exact (proj2 (BY1 i HI))|]. split; [exact BC|].
  eapply lframe_trans.
  - eapply lframe_implies; [exact E1|]. intros b pos (HNotA & HNotY & HNotX) HV; split; assumption.
  - eapply lframe_trans.
    + eapply lframe_implies; [exact E2|]. intros b pos (HNotA & HNotY & HNotX) HV; split; assumption.
    + eapply lframe_implies; [exact E3|]. intros b pos (HNotA & HNotY & HNotX) HV; split; assumption.
Qed.

Theorem curve_six_arithmetic_calls x y m ba b_y2 bx :
  square_input_bounds x -> square_input_bounds y -> ba<>b_y2 -> ba<>bx -> b_y2<>bx ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b_y2 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 m5 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y2 Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_add_int)
    [Vptr bx Ptrofs.zero;Vint (Int.repr 7)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_normalize_weak)
    [Vptr bx Ptrofs.zero] E0 m5 Vundef /\
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y2 Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf
    (Vint (if Z.eqb ((radix_value y * radix_value y) mod feP)
      ((radix_value x * radix_value x * radix_value x+7) mod feP) then Int.one else Int.zero)) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf b_y2 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  lframe (fun b _ => b<>ba /\ b<>b_y2 /\ b<>bx) m mf.
Proof.
  intros BX BY HAY HAX HYX HX HY HFA HFY HFX.
  destruct (curve_square_cube_calls x y m ba b_y2 bx BX BY HAY HAX HYX HX HY HFA HFY HFX)
    as (m1 & m2 & m3 & C1 & C2 & C3 & Y3 & X3 & A3X & A3Y & AF3 & YF3 & XF3 & VY & VC & BY3 & BX3 & FPrefix).
  destruct (curve_tail_calls (square_words y) (point_mul_words (square_words x) x)
    m3 b_y2 bx HYX BY3 BX3 Y3 X3 YF3 XF3)
    as (m4 & m5 & mf & C4 & C5 & C6 & YF6 & XF6 & FTail).
  pose proof (field_at_lframe m3 mf ba 0 (words5 x) _ A3X FTail
    ltac:(intro pos; split; assumption)) as A6X.
  pose proof (field_at_lframe m3 mf ba 40 (words5 y) _ A3Y FTail
    ltac:(intro pos; split; assumption)) as A6Y.
  pose proof (curve_keep_free _ m3 mf ba 88 ltac:(lia) AF3 FTail
    ltac:(intro pos; split; assumption)) as AF6.
  assert (HPlus : (radix_value (point_mul_words (square_words x) x)+7) mod feP =
    (radix_value x * radix_value x * radix_value x+7) mod feP).
  { transitivity ((radix_value (point_mul_words (square_words x) x) mod feP + 7) mod feP).
    - symmetry; apply Zplus_mod_idemp_l.
    - rewrite VC. apply Zplus_mod_idemp_l. }
  rewrite VY, HPlus in C6.
  exists m1,m2,m3,m4,m5,mf.
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [exact C4|]. split; [exact C5|]. split; [exact C6|].
  split; [exact A6X|]. split; [exact A6Y|]. split; [exact AF6|].
  split; [exact YF6|]. split; [exact XF6|].
  eapply lframe_trans; [exact FPrefix|].
  eapply lframe_implies; [exact FTail|]. intros b pos [_ [HNotY HNotX]] HV; split; assumption.
Qed.
