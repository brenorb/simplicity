(** The first five arithmetic calls of the original in-place point doubling.
    Derive all intermediate fields and ownership from the initial point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation
  C.jet_secp_point_square_coordinate C.jet_secp_gej_curve_coordinate C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_point_zy_multiply C.jet_secp_double_l_scale
  C.jet_secp_field_mul_small C.jet_secp_field_half_numeric.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words.

Definition double_work_frame (ba bs bl b : block) (_ : Z) := b<>ba /\ b<>bs /\ b<>bl.

Theorem double_prefix_calls x y z m ba bs bl :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> bs<>bl ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr ba (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
    [Vptr bl Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul_int)
    [Vptr bl Ptrofs.zero;Vint (Int.repr 3)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_half)
    [Vptr bl Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  fe_at mf ba 80 (words5 (point_mul_words z y)) /\
  fe_at mf bs 0 (words5 (square_words y)) /\
  fe_at mf bl 0 (words5 (double_l_words (square_words x))) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z y) /\
  mul_small_input_bounds (square_words y) /\
  square_input_bounds (double_l_words (square_words x)) /\
  radix_value (point_mul_words z y) mod feP=(radix_value z*radix_value y) mod feP /\
  radix_value (square_words y) mod feP=(radix_value y*radix_value y) mod feP /\
  radix_value (square_words x) mod feP=(radix_value x*radix_value x) mod feP /\
  2*radix_value (double_l_words (square_words x))=3*radix_value (square_words x)+
    half_parity (mul_small_words (Int.repr 3) (square_words x))*feP /\
  lframe (double_work_frame ba bs bl) m mf.
Proof.
  intros BX BY BZ HAS HAL HSL HX HY HZ HFA HFS HFL.
  destruct (eval_point_zy_mul_owned z y m ba BZ BY HZ HY HFA)
    as (m1 & C1 & Z1 & Y1 & AF1 & VZ & BZ1 & BTZ & F1).
  assert (X1 : fe_at m1 ba 0 (words5 x)).
  { eapply curve_keep_field_range;[reflexivity|exact HX|exact F1|].
    intros pos HP;right;left;lia. }
  pose proof (curve_keep_free _ m m1 bs 40 ltac:(lia) HFS F1
    ltac:(intro pos;left;congruence)) as SF1.
  pose proof (curve_keep_free _ m m1 bl 40 ltac:(lia) HFL F1
    ltac:(intro pos;left;congruence)) as LF1.
  destruct (eval_point_square_coordinate PointY y m1 bs ba BY SF1 Y1 AF1 (not_eq_sym HAS))
    as (m2 & C2 & S2 & SF2 & Y2 & AF2 & VS & BS2 & BTS & F2).
  pose proof (coordinate_frame_blocks PointY bs ba m1 m2 F2) as E2.
  pose proof (coordinate_frame_other PointY PointX x m1 m2 bs ba ltac:(discriminate)
    (not_eq_sym HAS) X1 F2) as X2.
  pose proof (coordinate_frame_other PointY PointZ (point_mul_words z y) m1 m2 bs ba
    ltac:(discriminate) (not_eq_sym HAS) Z1 F2) as Z2.
  pose proof (curve_keep_free _ m1 m2 bl 40 ltac:(lia) LF1 E2
    ltac:(intro pos;split;congruence)) as LF2.
  destruct (eval_point_square_coordinate PointX x m2 bl ba BX LF2 X2 AF2 (not_eq_sym HAL))
    as (m3 & C3 & L3 & LF3 & X3 & AF3 & VX & BL3 & BTL & F3).
  pose proof (coordinate_frame_blocks PointX bl ba m2 m3 F3) as E3.
  pose proof (coordinate_frame_other PointX PointY y m2 m3 bl ba ltac:(discriminate)
    (not_eq_sym HAL) Y2 F3) as Y3.
  pose proof (coordinate_frame_other PointX PointZ (point_mul_words z y) m2 m3 bl ba
    ltac:(discriminate) (not_eq_sym HAL) Z2 F3) as Z3.
  pose proof (field_at_lframe m2 m3 bs 0 _ _ S2 E3
    ltac:(intro pos;split;congruence)) as S3.
  pose proof (curve_keep_free _ m2 m3 bs 40 ltac:(lia) SF2 E3
    ltac:(intro pos;split;congruence)) as SF3.
  assert (BLT : mul_small_input_bounds (square_words x)).
  { intros i HI;exact (proj2 (BTL i HI)). }
  destruct (eval_double_l_scale (square_words x) m3 bl BLT L3 LF3)
    as (m4 & mf & C4 & C5 & L5 & LF5 & BL5 & VL & F45).
  pose proof (field_at_lframe m3 mf ba 0 _ _ X3 F45 ltac:(intro pos;congruence)) as X5.
  pose proof (field_at_lframe m3 mf ba 40 _ _ Y3 F45 ltac:(intro pos;congruence)) as Y5.
  pose proof (field_at_lframe m3 mf ba 80 _ _ Z3 F45 ltac:(intro pos;congruence)) as Z5.
  pose proof (field_at_lframe m3 mf bs 0 _ _ S3 F45 ltac:(intro pos;congruence)) as S5.
  pose proof (curve_keep_free _ m3 mf ba 128 ltac:(lia) AF3 F45 ltac:(intro pos;congruence)) as AF5.
  pose proof (curve_keep_free _ m3 mf bs 40 ltac:(lia) SF3 F45 ltac:(intro pos;congruence)) as SF5.
  exists m1,m2,m3,m4,mf.
  split;[exact C1|];split;[exact C2|];split;[exact C3|];split;[exact C4|];split;[exact C5|].
  split;[exact X5|];split;[exact Y5|];split;[exact Z5|];split;[exact S5|];split;[exact L5|].
  split;[exact AF5|];split;[exact SF5|];split;[exact LF5|];split;[exact BZ1|].
  split;[intros i HI;exact (proj2 (BTS i HI))|];split;[exact BL5|].
  split;[exact VZ|];split;[exact VS|];split;[exact VX|];split;[exact VL|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact F1|]. intros b pos (NA & NS & NL) HV;left;exact NA.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact E2|]. intros b pos (NA & NS & NL) HV;split;assumption.
    + eapply lframe_trans.
      * eapply lframe_implies;[exact E3|]. intros b pos (NA & NS & NL) HV;split;assumption.
      * eapply lframe_implies;[exact F45|]. intros b pos (NA & NS & NL) HV;exact NL.
Qed.
