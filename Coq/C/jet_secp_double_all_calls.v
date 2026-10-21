(** All fifteen arithmetic calls of the original in-place doubling, with
    output fields and writer bounds derived from initial storage.  Function
    entry/flag handling/freeing and the literal-specification bridge are not
    replaced by this intermediate execution theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame
  C.jet_secp_double_twelve C.jet_secp_double_y_tail C.jet_secp_double_prefix
  C.jet_secp_double_middle C.jet_secp_double_l_scale C.jet_secp_double_accumulate
  C.jet_secp_field_sum_bounds C.jet_secp_square_columns C.jet_secp_field_mul_small
  C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words double_t_words double_y_words.

Definition double_output_x_words x y := double_x_accum_words
  (square_words (double_l_words (square_words x))) (double_t_words x (square_words y)).
Definition double_output_t_words x y := double_t_accum_words
  (square_words (double_l_words (square_words x))) (double_t_words x (square_words y)).
Definition double_output_y_words x y := double_y_words (double_output_t_words x y)
  (double_l_words (square_words x)) (square_words (square_words y)).
Definition double_output_z_words y z := point_mul_words z y.

Theorem double_all_arithmetic_calls x y z m ba bs bl bt :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 mf,
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
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m8 Vundef /\
  Clight2.eval_funcall secp_ge m8 (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m9 Vundef /\
  Clight2.eval_funcall secp_ge m9 (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m10 Vundef /\
  Clight2.eval_funcall secp_ge m10 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero] E0 m11 Vundef /\
  Clight2.eval_funcall secp_ge m11 (Internal f_secp256k1_fe_add)
    [Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m12 Vundef /\
  Clight2.eval_funcall secp_ge m12 (Internal f_secp256k1_fe_mul)
    [Vptr ba (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m13 Vundef /\
  Clight2.eval_funcall secp_ge m13 (Internal f_secp256k1_fe_add)
    [Vptr ba (Ptrofs.repr 40);Vptr bs Ptrofs.zero] E0 m14 Vundef /\
  Clight2.eval_funcall secp_ge m14 (Internal f_secp256k1_fe_negate)
    [Vptr ba (Ptrofs.repr 40);Vptr ba (Ptrofs.repr 40);Vint (Int.repr 2)] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  lframe (fun b pos => double_work_frame ba bs bl b pos /\ b<>bt) m mf.
Proof.
  intros BX BY BZ HAS HAL HAT HSL HST HLT HX HY HZ HFA HFS HFL HFT.
  destruct (double_first_twelve_calls x y z m ba bs bl bt BX BY BZ HAS HAL HAT HSL HST HLT
    HX HY HZ HFA HFS HFL HFT)
    as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & m9 & m10 & m11 & m12 &
      C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 &
      X12 & Y12 & Z12 & S12 & L12 & T12 & AF12 & SF12 & LF12 & TF12 &
      BX12 & BT12 & BS12 & BL12 & BZ12 & F012).
  destruct (double_y_tail_calls (double_output_t_words x y) (double_l_words (square_words x))
    (square_words (square_words y)) m12 ba bt bl bs BT12 BL12 BS12 HAT HAL HAS
    (not_eq_sym HLT) (not_eq_sym HST) (not_eq_sym HSL) T12 L12 S12 AF12 TF12 LF12 SF12)
    as (m13 & m14 & mf & C13 & C14 & C15 & Y15 & T15 & L15 & S15 & AF15 & TF15 & LF15 & SF15 & BY15 & VY & F12F).
  assert (X15 : fe_at mf ba 0 (words5 (double_output_x_words x y))).
  { eapply curve_keep_field_range;[reflexivity|exact X12|exact F12F|].
    intros pos HP;unfold double_y_tail_frame;repeat split;try congruence;right;left;lia. }
  assert (Z15 : fe_at mf ba 80 (words5 (double_output_z_words y z))).
  { eapply curve_keep_field_range;[reflexivity|exact Z12|exact F12F|].
    intros pos HP;unfold double_y_tail_frame;repeat split;try congruence;right;right;lia. }
  exists m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,mf.
  split;[exact C1|];split;[exact C2|];split;[exact C3|];split;[exact C4|];split;[exact C5|].
  split;[exact C6|];split;[exact C7|];split;[exact C8|];split;[exact C9|];split;[exact C10|].
  split;[exact C11|];split;[exact C12|];split;[exact C13|];split;[exact C14|];split;[exact C15|].
  split;[exact X15|];split;[exact Y15|];split;[exact Z15|].
  split;[exact AF15|];split;[exact SF15|];split;[exact LF15|];split;[exact TF15|].
  split;[exact (field_scaled_loose 3 _ ltac:(lia) BX12)|];split;[exact BY15|];split;[exact BZ12|].
  eapply lframe_trans;[exact F012|].
  eapply lframe_implies;[exact F12F|]. intros b pos [(NA & NS & NL) NT] HV.
  unfold double_y_tail_frame;repeat split;try assumption;left;exact NA.
Qed.
