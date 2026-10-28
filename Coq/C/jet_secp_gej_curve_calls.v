(** Nine original C arithmetic calls for the full projective check, in order.
    Inputs include arbitrary represented coordinates, including Z=0. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_field_read_preservation.
Require Import C.jet_secp_gej_curve_prefix C.jet_secp_gej_curve_tail C.jet_secp_gej_curve_literal_numeric
  C.jet_secp_curve_frame C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Theorem gej_curve_arithmetic_calls_readback x y z m ba b_y bx bz :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 m5 m6 m7 m8 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_mul)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m5 Vundef /\
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m6 Vundef /\
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul_int)
    [Vptr bz Ptrofs.zero;Vint (Int.repr 7)] E0 m7 Vundef /\
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_add)
    [Vptr bx Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m8 Vundef /\
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf
    (Vint (if Z.eqb ((radix_value y*radix_value y) mod feP)
      ((radix_value x*radix_value x*radix_value x+
        7*(radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z)) mod feP)
      then Int.one else Int.zero)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  lframe (gej_curve_frame ba b_y bx bz) m mf /\ gej_curve_input_readback m mf ba x y z.
Proof.
  intros BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
  destruct (gej_curve_prefix_calls_readback x y z m ba b_y bx bz BX BY BZ
    HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ)
    as (m1 & m2 & m3 & m4 & m5 & C1 & C2 & C3 & C4 & C5 & Y5 & X5 & Z5 & AF5 &
      YF5 & XF5 & ZF5 & VY & VX & VZ & BY5 & BX5 & BZ5 & FP & Read5).
  destruct (gej_curve_tail_calls (square_words y) (point_mul_words (square_words x) x)
    (point_mul_words (square_words z) z) m5 b_y bx bz BY5 BX5 BZ5 HYX HYZ HXZ Y5 X5 Z5 YF5 XF5 ZF5)
    as (m6 & m7 & m8 & mf & C6 & C7 & C8 & C9 & YF9 & XF9 & ZF9 & FT).
  pose proof (curve_keep_free _ m5 mf ba 128 ltac:(lia) AF5 FT
    ltac:(intro pos;repeat split;assumption)) as AF9.
  assert (HRight :
    (radix_value (point_mul_words (square_words x) x)+
     7*(radix_value (point_mul_words (square_words z) z)*radix_value (point_mul_words (square_words z) z))) mod feP=
    (radix_value x*radix_value x*radix_value x+
     7*(radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z)) mod feP).
  { rewrite (Z.add_mod (radix_value (point_mul_words (square_words x) x))
      (7*(radix_value (point_mul_words (square_words z) z)*radix_value (point_mul_words (square_words z) z))) feP),
      (Z.add_mod (radix_value x*radix_value x*radix_value x)
      (7*(radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z)) feP),VX,
      (Z.mul_mod 7 (radix_value (point_mul_words (square_words z) z)*radix_value (point_mul_words (square_words z) z)) feP),
      (Z.mul_mod 7 (radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z) feP),
      (Z.mul_mod (radix_value (point_mul_words (square_words z) z))
        (radix_value (point_mul_words (square_words z) z)) feP),VZ,gej_curve_six_mod
      by (unfold feP,feR;lia);reflexivity. }
  rewrite VY,HRight in C9.
  exists m1,m2,m3,m4,m5,m6,m7,m8,mf.
  split;[exact C1|]. split;[exact C2|]. split;[exact C3|]. split;[exact C4|]. split;[exact C5|].
  split;[exact C6|]. split;[exact C7|]. split;[exact C8|]. split;[exact C9|].
  split;[exact AF9|]. split;[exact YF9|]. split;[exact XF9|]. split;[exact ZF9|].
  assert (FullFrame:lframe (gej_curve_frame ba b_y bx bz) m mf).
  {
  eapply lframe_trans;[exact FP|]. eapply lframe_implies;[exact FT|].
  intros b pos (NA & NY & NX & NZ) HV;repeat split;assumption.
  }

  split;[exact FullFrame|].
  destruct Read5 as (AX5 & AY5 & AZ5 & Flag5).
  unfold gej_curve_input_readback;split.
  - eapply field_at_lframe;[exact AX5|exact FT|intros;repeat split;congruence].
  - split.
    + eapply field_at_lframe;[exact AY5|exact FT|intros;repeat split;congruence].
    + split.
      * eapply field_at_lframe;[exact AZ5|exact FT|intros;repeat split;congruence].
      * rewrite (proj1 FT Mint32 ba 120);[exact Flag5| |intros;repeat split;congruence].
        eapply Mem.perm_valid_block;apply (AF5 0);lia.
Qed.

Theorem gej_curve_arithmetic_calls x y z m ba b_y bx bz :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 m5 m6 m7 m8 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b_y Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_mul)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero;Vptr ba (Ptrofs.repr 80)] E0 m5 Vundef /\
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_sqr)
    [Vptr bz Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m6 Vundef /\
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul_int)
    [Vptr bz Ptrofs.zero;Vint (Int.repr 7)] E0 m7 Vundef /\
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_add)
    [Vptr bx Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m8 Vundef /\
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf
    (Vint (if Z.eqb ((radix_value y*radix_value y) mod feP)
      ((radix_value x*radix_value x*radix_value x+
        7*(radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z)) mod feP)
      then Int.one else Int.zero)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  lframe (gej_curve_frame ba b_y bx bz) m mf.
Proof.
 intros BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
 destruct (gej_curve_arithmetic_calls_readback x y z m ba b_y bx bz BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ) as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & mf & Rest).
 exists m1,m2,m3,m4,m5,m6,m7,m8,mf;tauto.
Qed.
