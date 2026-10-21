(** Twelve actual arithmetic calls from the initial point and three private
    allocations.  The final Y multiplication/negation and full helper lifecycle
    are still separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_double_front C.jet_secp_double_prefix
  C.jet_secp_double_middle C.jet_secp_double_l_scale C.jet_secp_double_accumulate
  C.jet_secp_field_sum_bounds C.jet_secp_field_mul_small C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words double_t_words.

Theorem double_first_twelve_calls x y z m ba bs bl bt :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  let lx := double_l_words (square_words x) in
  let x8 := square_words lx in
  let t8 := double_t_words x (square_words y) in
  exists m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 mf,
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
    [Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_x_accum_words x8 t8)) /\
  fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 (point_mul_words z y)) /\
  fe_at mf bs 0 (words5 (square_words (square_words y))) /\ fe_at mf bl 0 (words5 lx) /\
  fe_at mf bt 0 (words5 (double_t_accum_words x8 t8)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  field_scaled_bounds 3 (double_x_accum_words x8 t8) /\
  square_input_bounds (double_t_accum_words x8 t8) /\
  mul_small_input_bounds (square_words (square_words y)) /\
  square_input_bounds lx /\ square_input_bounds (point_mul_words z y) /\
  lframe (fun b pos => double_work_frame ba bs bl b pos /\ b<>bt) m mf.
Proof.
  intros BX BY BZ HAS HAL HAT HSL HST HLT HX HY HZ HFA HFS HFL HFT;cbn zeta.
  destruct (double_front_calls x y z m ba bs bl bt BX BY BZ HAS HAL HAT HSL HST HLT
    HX HY HZ HFA HFS HFL HFT)
    as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 &
      X8 & Y8 & Z8 & S8 & L8 & T8 & AF8 & SF8 & LF8 & TF8 & BX8 & BT8 & BS8 & BL8 & BZ8 & F18).
  assert (BSL : square_input_bounds (square_words y)).
  { exact (field_scaled_loose 1 _ ltac:(lia) (field_tight_scaled _ BS8)). }
  destruct (double_accumulate_calls _ _ _ m8 ba bt bs BX8 BT8 BSL HAT HAS (not_eq_sym HST)
    X8 T8 S8 AF8 TF8 SF8)
    as (m9 & m10 & m11 & mf & C9 & C10 & C11 & C12 & XF & TF & SF & AFF & TFF & SFF &
      BXF & BTF & BSF & VXF & VTF & VSF & F8F).
  assert (YF : fe_at mf ba 40 (words5 y)).
  { eapply curve_keep_field_range;[reflexivity|exact Y8|exact F8F|].
    intros pos HP;unfold double_accum_frame;repeat split;try congruence;right;right;lia. }
  assert (ZF : fe_at mf ba 80 (words5 (point_mul_words z y))).
  { eapply curve_keep_field_range;[reflexivity|exact Z8|exact F8F|].
    intros pos HP;unfold double_accum_frame;repeat split;try congruence;right;right;lia. }
  pose proof (field_at_lframe m8 mf bl 0 _ _ L8 F8F
    ltac:(intro pos;unfold double_accum_frame;repeat split;try congruence;left;congruence)) as LF.
  pose proof (curve_keep_free _ m8 mf bl 40 ltac:(lia) LF8 F8F
    ltac:(intro pos;unfold double_accum_frame;repeat split;try congruence;left;congruence)) as LFF.
  exists m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,mf.
  split;[exact C1|];split;[exact C2|];split;[exact C3|];split;[exact C4|];split;[exact C5|];split;[exact C6|].
  split;[exact C7|];split;[exact C8|];split;[exact C9|];split;[exact C10|];split;[exact C11|];split;[exact C12|].
  split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact SF|];split;[exact LF|];split;[exact TF|].
  split;[exact AFF|];split;[exact SFF|];split;[exact LFF|];split;[exact TFF|].
  split;[exact BXF|];split;[exact (field_scaled_loose 4 _ ltac:(lia) BTF)|].
  split;[exact BSF|];split;[exact BL8|];split;[exact BZ8|].
  eapply lframe_trans;[exact F18|].
  eapply lframe_implies;[exact F8F|]. intros b pos [(HA & HS & HL) HT] HV.
  unfold double_accum_frame;repeat split;try assumption;left;exact HA.
Qed.
