(** Actual doubling calls nine through twelve: X += T twice, S = S^2,
    T += X.  All memory, limb bounds and value identities follow from the
    input storage, without post-call premises or inserted normalizations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math
  C.jet_secp_point_write_run C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_point_field_add C.jet_secp_field_sum_bounds C.jet_secp_field_add_scaled
  C.jet_secp_field_mul_small C.jet_secp_square_inplace_storage C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition double_x_accum_words x t := field_sum_words (field_sum_words x t) t.
Definition double_t_accum_words x t := field_sum_words t (double_x_accum_words x t).
Definition double_accum_frame (ba bt bs b : block) (pos : Z) :=
  b<>bt /\ b<>bs /\ (b<>ba \/ pos<0 \/ 40<=pos).

Theorem double_accumulate_calls x t s m ba bt bs :
  mul_small_input_bounds x -> mul_small_input_bounds t -> square_input_bounds s ->
  ba<>bt -> ba<>bs -> bt<>bs ->
  fe_at m ba 0 (words5 x) -> fe_at m bt 0 (words5 t) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable ->
  exists m1 m2 m3 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_add)
    [Vptr ba Ptrofs.zero;Vptr bt Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
    [Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero] E0 m3 Vundef /\
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_add)
    [Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_x_accum_words x t)) /\
  fe_at mf bt 0 (words5 (double_t_accum_words x t)) /\
  fe_at mf bs 0 (words5 (square_words s)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\
  field_scaled_bounds 3 (double_x_accum_words x t) /\
  field_scaled_bounds 4 (double_t_accum_words x t) /\
  mul_small_input_bounds (square_words s) /\
  radix_value (double_x_accum_words x t)=radix_value x+2*radix_value t /\
  radix_value (double_t_accum_words x t)=radix_value x+3*radix_value t /\
  radix_value (square_words s) mod feP=(radix_value s*radix_value s) mod feP /\
  lframe (double_accum_frame ba bt bs) m mf.
Proof.
  intros BX BT BS HAT HAS HTS HX HT HS HFA HFT HFS.
  destruct (eval_point_field_add true PointX x t m ba bt HAT HX HFA HT HFT)
    as (m1 & C1 & X1 & T1 & AF1 & TF1 & F1).
  destruct (eval_point_field_add true PointX (field_sum_words x t) t m1 ba bt HAT X1 AF1 T1 TF1)
    as (m2 & C2 & X2 & T2 & AF2 & TF2 & F2).
  pose proof (lframe_trans _ m m1 m2 F1 F2) as F12.
  pose proof (field_at_lframe m m2 bs 0 _ _ HS F12
    ltac:(intro pos;split;[congruence|left;congruence])) as S2.
  pose proof (curve_keep_free _ m m2 bs 40 ltac:(lia) HFS F12
    ltac:(intro pos;split;[congruence|left;congruence])) as SF2.
  destruct (eval_square_inplace_from_storage s m2 bs BS S2 SF2)
    as (m3 & C3 & S3 & SF3 & VS & BS3 & BTS & F3).
  pose proof (field_at_lframe m2 m3 ba 0 _ _ X2 F3 ltac:(intro pos;congruence)) as X3.
  pose proof (field_at_lframe m2 m3 bt 0 _ _ T2 F3 ltac:(intro pos;congruence)) as T3.
  pose proof (curve_keep_free _ m2 m3 ba 128 ltac:(lia) AF2 F3 ltac:(intro pos;congruence)) as AF3.
  pose proof (curve_keep_free _ m2 m3 bt 40 ltac:(lia) TF2 F3 ltac:(intro pos;congruence)) as TF3.
  destruct (eval_point_field_add false PointX (double_x_accum_words x t) t m3 ba bt HAT X3 AF3 T3 TF3)
    as (mf & C4 & X4 & T4 & AF4 & TF4 & F4).
  pose proof (field_at_lframe m3 mf bs 0 _ _ S3 F4
    ltac:(intro pos;split;[congruence|left;congruence])) as S4.
  pose proof (curve_keep_free _ m3 mf bs 40 ltac:(lia) SF3 F4
    ltac:(intro pos;split;[congruence|left;congruence])) as SF4.
  destruct (field_sum_twice_value x t BX BT) as [VX BXX].
  fold (double_x_accum_words x t) in VX,BXX.
  pose proof (field_tight_scaled t BT) as BT1.
  pose proof (field_sum_scaled_bounds 1 3 t (double_x_accum_words x t)
    ltac:(lia) ltac:(lia) ltac:(lia) BT1 BXX) as BTT.
  assert (VT : radix_value (double_t_accum_words x t)=radix_value x+3*radix_value t).
  { unfold double_t_accum_words;rewrite field_sum_exact_value.
    - rewrite VX;ring.
    - exact (field_sum_scaled_no_overflow 1 3 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BT1 BXX). }
  exists m1,m2,m3,mf;split;[exact C1|];split;[exact C2|];split;[exact C3|];split;[exact C4|].
  split;[exact X4|];split;[exact T4|];split;[exact S4|];split;[exact AF4|];split;[exact TF4|];split;[exact SF4|].
  split;[exact BXX|];split;[exact BTT|];split;[intros i HI;exact (proj2 (BTS i HI))|].
  split;[exact VX|];split;[exact VT|];split;[exact VS|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact F12|]. intros b pos (NT & NS & NA) HV;split;assumption.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact F3|]. intros b pos (NT & NS & NA) HV;exact NS.
    + eapply lframe_implies;[exact F4|]. intros b pos (NT & NS & NA) HV;split;assumption.
Qed.
