(** First eight actual doubling calls from initial owned storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math
  C.jet_secp_curve_frame C.jet_secp_double_prefix C.jet_secp_double_middle C.jet_secp_double_l_scale
  C.jet_secp_field_mul_small C.jet_secp_field_half_numeric C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words double_t_words.

Theorem double_front_calls x y z m ba bs bl bt :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 m5 m6 m7 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr ba (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 80);Vptr ba (Ptrofs.repr 40)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr ba (Ptrofs.repr 40)] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
    [Vptr bl Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul_int)
    [Vptr bl Ptrofs.zero;Vint (Int.repr 3)] E0 m4 Vundef /\
  Clight2.eval_funcall secp_ge m4 (Internal f_secp256k1_fe_half)
    [Vptr bl Ptrofs.zero] E0 m5 Vundef /\
  Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_negate)
    [Vptr bt Ptrofs.zero;Vptr bs Ptrofs.zero;Vint Int.one] E0 m6 Vundef /\
  Clight2.eval_funcall secp_ge m6 (Internal f_secp256k1_fe_mul)
    [Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m7 Vundef /\
  Clight2.eval_funcall secp_ge m7 (Internal f_secp256k1_fe_sqr)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (square_words (double_l_words (square_words x)))) /\
  fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 (point_mul_words z y)) /\
  fe_at mf bs 0 (words5 (square_words y)) /\
  fe_at mf bl 0 (words5 (double_l_words (square_words x))) /\
  fe_at mf bt 0 (words5 (double_t_words x (square_words y))) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  mul_small_input_bounds (square_words (double_l_words (square_words x))) /\
  mul_small_input_bounds (double_t_words x (square_words y)) /\
  mul_small_input_bounds (square_words y) /\
  square_input_bounds (double_l_words (square_words x)) /\ square_input_bounds (point_mul_words z y) /\
  lframe (fun b pos => double_work_frame ba bs bl b pos /\ b<>bt) m mf.
Proof.
  intros BX BY BZ HAS HAL HAT HSL HST HLT HX HY HZ HFA HFS HFL HFT.
  destruct (double_prefix_calls x y z m ba bs bl BX BY BZ HAS HAL HSL HX HY HZ HFA HFS HFL)
    as (m1 & m2 & m3 & m4 & m5 & C1 & C2 & C3 & C4 & C5 & X5 & Y5 & Z5 & S5 & L5 &
      AF5 & SF5 & LF5 & BZ5 & BS5 & BL5 & VZ & VS & VX & VL & F15).
  pose proof (curve_keep_free _ m m5 bt 40 ltac:(lia) HFT F15
    ltac:(intro pos;unfold double_work_frame;repeat split;congruence)) as TF5.
  destruct (double_middle_calls x (square_words y) (double_l_words (square_words x)) m5 ba bs bl bt
    BX BS5 BL5 HAS HAL HAT HSL HST HLT X5 S5 L5 AF5 SF5 LF5 TF5)
    as (m6 & m7 & mf & C6 & C7 & C8 & X8 & S8 & L8 & T8 & AF8 & SF8 & LF8 & TF8 &
      BX8 & BT8 & VT & VX8 & F58).
  assert (Y8 : fe_at mf ba 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y5|exact F58|].
    intros pos HP;unfold double_middle_frame;repeat split;try congruence;right;right;lia. }
  assert (Z8 : fe_at mf ba 80 (words5 (point_mul_words z y))).
  { eapply curve_keep_field_range;[reflexivity|exact Z5|exact F58|].
    intros pos HP;unfold double_middle_frame;repeat split;try congruence;right;right;lia. }
  exists m1,m2,m3,m4,m5,m6,m7,mf.
  split;[exact C1|];split;[exact C2|];split;[exact C3|];split;[exact C4|];split;[exact C5|].
  split;[exact C6|];split;[exact C7|];split;[exact C8|].
  split;[exact X8|];split;[exact Y8|];split;[exact Z8|];split;[exact S8|];split;[exact L8|];split;[exact T8|].
  split;[exact AF8|];split;[exact SF8|];split;[exact LF8|];split;[exact TF8|].
  split;[exact BX8|];split;[exact BT8|];split;[exact BS5|];split;[exact BL5|];split;[exact BZ5|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact F15|]. intros b pos [HF HT] HV;exact HF.
  - eapply lframe_implies;[exact F58|]. intros b pos [(HA & HS & HL) HT] HV.
    unfold double_middle_frame;repeat split;try assumption;left;exact HA.
Qed.
