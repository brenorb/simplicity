(** The first five actual calls of simplicity_gej_is_valid_var, from owned
    point storage and fresh temporaries; every intermediate call is derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_point_write_run C.jet_secp_point_square_coordinate
  C.jet_secp_gej_curve_coordinate C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition gej_curve_frame (ba b_y bx bz : block) :=
  fun b : block => fun _ : Z => b<>ba /\ b<>b_y /\ b<>bx /\ b<>bz.

Definition gej_curve_input_readback m mf ba x y z :=
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Mem.load Mint32 m ba 120.


Lemma coordinate_frame_flag_readback k bout bin m mf :
 bout<>bin -> Mem.valid_block m bin ->
 lframe (point_square_coordinate_frame k bout bin) m mf ->
 Mem.load Mint32 mf bin 120=Mem.load Mint32 m bin 120.
Proof.
 intros Different Valid Frame;apply (proj1 Frame);[exact Valid|].
 intros pos Range;unfold point_square_coordinate_frame;intros [[Same _]|[_ At]].
 - congruence.
 - destruct k;cbn [point_coordinate_offset] in At;cbn [size_chunk] in Range;lia.
Qed.

Theorem gej_curve_prefix_calls_readback x y z m ba b_y bx bz :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_mul)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 mf Vundef /\
  fe_at mf b_y 0 (words5 (square_words y)) /\
  fe_at mf bx 0 (words5 (point_mul_words (square_words x) x)) /\
  fe_at mf bz 0 (words5 (point_mul_words (square_words z) z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  radix_value (square_words y) mod feP=(radix_value y*radix_value y) mod feP /\
  radix_value (point_mul_words (square_words x) x) mod feP=(radix_value x*radix_value x*radix_value x) mod feP /\
  radix_value (point_mul_words (square_words z) z) mod feP=(radix_value z*radix_value z*radix_value z) mod feP /\
  (forall i, (i<5)%nat -> Int64.unsigned (square_words y i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  (forall i, (i<5)%nat -> Int64.unsigned (point_mul_words (square_words x) x i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  square_input_bounds (point_mul_words (square_words z) z) /\
  lframe (gej_curve_frame ba b_y bx bz) m mf /\ gej_curve_input_readback m mf ba x y z.
Proof.
  intros BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
  destruct (eval_point_square_coordinate PointY y m b_y ba BY HFY HY HFA (not_eq_sym HAY))
    as (m1 & C1 & Y1 & YF1 & A1Y & AF1 & VY & BY1 & BTY & F1).
  pose proof (coordinate_frame_blocks PointY b_y ba m m1 F1) as E1.
  pose proof (coordinate_frame_other PointY PointX x m m1 b_y ba ltac:(discriminate)
    (not_eq_sym HAY) HX F1) as A1X.
  pose proof (coordinate_frame_other PointY PointZ z m m1 b_y ba ltac:(discriminate)
    (not_eq_sym HAY) HZ F1) as A1Z.
  pose proof (curve_keep_free _ m m1 bx 40 ltac:(lia) HFX E1 ltac:(intro pos;split;congruence)) as XF1.
  pose proof (curve_keep_free _ m m1 bz 40 ltac:(lia) HFZ E1 ltac:(intro pos;split;congruence)) as ZF1.
  destruct (coordinate_square_cube_calls PointX x m1 bx ba BX (not_eq_sym HAX) XF1 A1X AF1)
    as (m2 & m3 & C2 & C3 & X3 & XF3 & A3X & AF3 & VX & BX3 & BTX & F23).
  pose proof (coordinate_frame_blocks PointX bx ba m1 m3 F23) as E23.
  pose proof (coordinate_frame_other PointX PointZ z m1 m3 bx ba ltac:(discriminate)
    (not_eq_sym HAX) A1Z F23) as A3Z.
  pose proof (field_at_lframe m1 m3 b_y 0 _ _ Y1 E23 ltac:(intro pos;split;congruence)) as Y3.
  pose proof (curve_keep_free _ m1 m3 b_y 40 ltac:(lia) YF1 E23 ltac:(intro pos;split;congruence)) as YF3.
  pose proof (curve_keep_free _ m1 m3 bz 40 ltac:(lia) ZF1 E23 ltac:(intro pos;split;congruence)) as ZF3.
  destruct (coordinate_square_cube_calls PointZ z m3 bz ba BZ (not_eq_sym HAZ) ZF3 A3Z AF3)
    as (m4 & mf & C4 & C5 & Z5 & ZF5 & A5Z & AF5 & VZ & BZ5 & BTZ & F45).
  pose proof (coordinate_frame_blocks PointZ bz ba m3 mf F45) as E45.
  pose proof (field_at_lframe m3 mf b_y 0 _ _ Y3 E45 ltac:(intro pos;split;congruence)) as Y5.
  pose proof (field_at_lframe m3 mf bx 0 _ _ X3 E45 ltac:(intro pos;split;congruence)) as X5.
  pose proof (curve_keep_free _ m3 mf b_y 40 ltac:(lia) YF3 E45 ltac:(intro pos;split;congruence)) as YF5.
  pose proof (curve_keep_free _ m3 mf bx 40 ltac:(lia) XF3 E45 ltac:(intro pos;split;congruence)) as XF5.
  exists m1,m2,m3,m4,mf.
  split;[exact C1|]. split;[exact C2|]. split;[exact C3|]. split;[exact C4|]. split;[exact C5|].
  split;[exact Y5|]. split;[exact X5|]. split;[exact Z5|]. split;[exact AF5|].
  split;[exact YF5|]. split;[exact XF5|]. split;[exact ZF5|].
  split;[exact VY|]. split;[exact VX|]. split;[exact VZ|].
  split;[intros i HI;exact (proj2 (BTY i HI))|]. split;[exact BTX|]. split;[exact BZ5|].
  assert (FullFrame:lframe (gej_curve_frame ba b_y bx bz) m mf).
  {
  eapply lframe_trans.
  - eapply lframe_implies;[exact E1|]. intros b pos (NA & NY & NX & NZ) HV;split;assumption.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact E23|]. intros b pos (NA & NY & NX & NZ) HV;split;assumption.
    + eapply lframe_implies;[exact E45|]. intros b pos (NA & NY & NX & NZ) HV;split;assumption.
  }

  split;[exact FullFrame|].
  unfold gej_curve_input_readback.
  assert (A5X:fe_at mf ba 0 (words5 x)).
  { exact (coordinate_frame_other PointZ PointX x m3 mf bz ba ltac:(discriminate)
     (not_eq_sym HAZ) A3X F45). }
  assert (A3Y:fe_at m3 ba 40 (words5 y)).
  { exact (coordinate_frame_other PointX PointY y m1 m3 bx ba ltac:(discriminate)
     (not_eq_sym HAX) A1Y F23). }
  assert (A5Y:fe_at mf ba 40 (words5 y)).
  { exact (coordinate_frame_other PointZ PointY y m3 mf bz ba ltac:(discriminate)
     (not_eq_sym HAZ) A3Y F45). }
  split;[exact A5X|];split;[exact A5Y|];split;[exact A5Z|].
  rewrite (coordinate_frame_flag_readback PointZ bz ba m3 mf (not_eq_sym HAZ)
    ltac:(eapply Mem.perm_valid_block;apply (AF3 0);lia) F45).
  rewrite (coordinate_frame_flag_readback PointX bx ba m1 m3 (not_eq_sym HAX)
    ltac:(eapply Mem.perm_valid_block;apply (AF1 0);lia) F23).
  apply (coordinate_frame_flag_readback PointY b_y ba m m1 (not_eq_sym HAY)
    ltac:(eapply Mem.perm_valid_block;apply (HFA 0);lia) F1).
Qed.

Theorem gej_curve_prefix_calls x y z m ba b_y bx bz :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_mul)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 mf Vundef /\
  fe_at mf b_y 0 (words5 (square_words y)) /\
  fe_at mf bx 0 (words5 (point_mul_words (square_words x) x)) /\
  fe_at mf bz 0 (words5 (point_mul_words (square_words z) z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  radix_value (square_words y) mod feP=(radix_value y*radix_value y) mod feP /\
  radix_value (point_mul_words (square_words x) x) mod feP=(radix_value x*radix_value x*radix_value x) mod feP /\
  radix_value (point_mul_words (square_words z) z) mod feP=(radix_value z*radix_value z*radix_value z) mod feP /\
  (forall i, (i<5)%nat -> Int64.unsigned (square_words y i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  (forall i, (i<5)%nat -> Int64.unsigned (point_mul_words (square_words x) x i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  square_input_bounds (point_mul_words (square_words z) z) /\
  lframe (gej_curve_frame ba b_y bx bz) m mf.
Proof.
 intros BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
 destruct (gej_curve_prefix_calls_readback x y z m ba b_y bx bz BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ) as (m1 & m2 & m3 & m4 & mf & Rest).
 exists m1,m2,m3,m4,mf;tauto.
Qed.
