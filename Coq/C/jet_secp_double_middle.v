(** Calls six through eight of gej_double: negate S into T, multiply T by X,
    and square L into X.  The point's Y/Z/flag bytes are framed, not reset. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math
  C.jet_secp_point_write_run C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_field_negate_separate C.jet_secp_field_point_multiply C.jet_secp_square_point_x
  C.jet_secp_field_mul_small C.jet_secp_square_columns C.jet_secp_square_numeric
  C.jet_secp_gej_curve_coordinate C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words negate_sep_words.

Definition double_t_words x s := point_mul_words (negate_sep_words s) x.
Definition double_middle_frame (ba bs bl bt b : block) (pos : Z) :=
  b<>bs /\ b<>bl /\ b<>bt /\ (b<>ba \/ pos<0 \/ 40<=pos).

Theorem double_middle_calls x s l m ba bs bl bt :
  square_input_bounds x -> mul_small_input_bounds s -> square_input_bounds l ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m bs 0 (words5 s) -> fe_at m bl 0 (words5 l) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists m1 m2 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bt Ptrofs.zero;Vptr bs Ptrofs.zero;Vint Int.one] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
    [Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
    [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (square_words l)) /\ fe_at mf bs 0 (words5 s) /\
  fe_at mf bl 0 (words5 l) /\ fe_at mf bt 0 (words5 (double_t_words x s)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  mul_small_input_bounds (square_words l) /\ mul_small_input_bounds (double_t_words x s) /\
  radix_value (double_t_words x s) mod feP=((4*feP-radix_value s)*radix_value x) mod feP /\
  radix_value (square_words l) mod feP=(radix_value l*radix_value l) mod feP /\
  lframe (double_middle_frame ba bs bl bt) m mf.
Proof.
  intros BX BS BL HAS HAL HAT HSL HST HLT HX HS HL HFA HFS HFL HFT.
  destruct (eval_negate_sep_from_storage s m bt bs BS (not_eq_sym HST) HFT HS HFS)
    as (m1 & C1 & T1 & S1 & TF1 & SF1 & VN & BN & F1).
  pose proof (field_at_lframe m m1 ba 0 _ _ HX F1 ltac:(intro pos;split;congruence)) as X1.
  pose proof (field_at_lframe m m1 bl 0 _ _ HL F1 ltac:(intro pos;split;congruence)) as L1.
  pose proof (curve_keep_free _ m m1 ba 128 ltac:(lia) HFA F1
    ltac:(intro pos;split;congruence)) as AF1.
  pose proof (curve_keep_free _ m m1 bl 40 ltac:(lia) HFL F1
    ltac:(intro pos;split;congruence)) as LF1.
  destruct (eval_field_point_mul_numeric PointX (negate_sep_words s) x m1 bt ba BN BX
    (not_eq_sym HAT) T1 TF1 X1 AF1)
    as (m2 & C2 & T2 & TF2 & X2 & AF2 & VT & BT2 & BTT & F2).
  pose proof (coordinate_frame_blocks PointX bt ba m1 m2 F2) as E2.
  pose proof (field_at_lframe m1 m2 bs 0 _ _ S1 E2 ltac:(intro pos;split;congruence)) as S2.
  pose proof (field_at_lframe m1 m2 bl 0 _ _ L1 E2 ltac:(intro pos;split;congruence)) as L2.
  pose proof (curve_keep_free _ m1 m2 bs 40 ltac:(lia) SF1 E2
    ltac:(intro pos;split;congruence)) as SF2.
  pose proof (curve_keep_free _ m1 m2 bl 40 ltac:(lia) LF1 E2
    ltac:(intro pos;split;congruence)) as LF2.
  destruct (eval_square_point_x l m2 ba bl BL AF2 L2 LF2 HAL)
    as (mf & C3 & X3 & AF3 & L3 & LF3 & VX & BX3 & BTX & F3).
  assert (E3 : lframe (fun b _ => b<>ba /\ b<>bl) m2 mf).
  { eapply lframe_implies;[exact F3|]. intros b pos [NA NL] HV.
    unfold square_two_ranges;intros [[HE _]|[HE _]];congruence. }
  pose proof (field_at_lframe m2 mf bs 0 _ _ S2 E3 ltac:(intro pos;split;congruence)) as S3.
  pose proof (field_at_lframe m2 mf bt 0 _ _ T2 E3 ltac:(intro pos;split;congruence)) as T3.
  pose proof (curve_keep_free _ m2 mf bs 40 ltac:(lia) SF2 E3
    ltac:(intro pos;split;congruence)) as SF3.
  pose proof (curve_keep_free _ m2 mf bt 40 ltac:(lia) TF2 E3
    ltac:(intro pos;split;congruence)) as TF3.
  rewrite VN in VT.
  exists m1,m2,mf;split;[exact C1|];split;[exact C2|];split;[exact C3|].
  split;[exact X3|];split;[exact S3|];split;[exact L3|];split;[exact T3|].
  split;[exact AF3|];split;[exact SF3|];split;[exact LF3|];split;[exact TF3|].
  split;[exact BTX|];split;[exact BTT|];split;[exact VT|];split;[exact VX|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact F1|]. intros b pos (NS & NL & NT & NA) HV;split;assumption.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact F2|]. intros b pos (NS & NL & NT & NA) HV.
      intros [[HE HP]|[HE HP]].
      * congruence.
      * subst b;change (0<=pos<40) in HP;destruct NA as [NA|[NA|NA]];[contradiction|lia|lia].
    + eapply lframe_implies;[exact F3|]. intros b pos (NS & NL & NT & NA) HV.
      unfold square_two_ranges;intros [[HE HP]|[HE HP]].
      * subst b;destruct NA as [NA|[NA|NA]];[contradiction|lia|lia].
      * congruence.
Qed.
