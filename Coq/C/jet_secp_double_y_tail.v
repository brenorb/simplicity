(** Last three original arithmetic calls of gej_double, deriving Y and the
    preserved source fields from actual caller storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_point_write_run
  C.jet_secp_point_y_product C.jet_secp_point_y_negate2 C.jet_secp_point_field_add
  C.jet_secp_field_add_scaled C.jet_secp_field_sum_bounds C.jet_secp_field_mul_small
  C.jet_secp_square_columns C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words point_y_neg2_words.

Definition double_y_words t l s := point_y_neg2_words (field_sum_words (point_mul_words t l) s).
Definition double_y_tail_frame (bp bt bl bs b : block) (pos : Z) :=
  b<>bt /\ b<>bl /\ b<>bs /\ (b<>bp \/ pos<40 \/ 80<=pos).

Theorem double_y_tail_calls t l s m bp bt bl bs :
  square_input_bounds t -> square_input_bounds l -> mul_small_input_bounds s ->
  bp<>bt -> bp<>bl -> bp<>bs -> bt<>bl -> bt<>bs -> bl<>bs ->
  fe_at m bt 0 (words5 t) -> fe_at m bl 0 (words5 l) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  exists m1 m2 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vptr bl Ptrofs.zero] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_add)
    [Vptr bp (Ptrofs.repr 40);Vptr bs Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_negate)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vint (Int.repr 2)] E0 mf Vundef /\
  fe_at mf bp 40 (words5 (double_y_words t l s)) /\
  fe_at mf bt 0 (words5 t) /\ fe_at mf bl 0 (words5 l) /\ fe_at mf bs 0 (words5 s) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  square_input_bounds (double_y_words t l s) /\
  radix_value (double_y_words t l s)=6*feP-radix_value (point_mul_words t l)-radix_value s /\
  lframe (double_y_tail_frame bp bt bl bs) m mf.
Proof.
  intros BT BL BS HPT HPL HPS HTL HTS HLS HT HL HS HFP HFT HFL HFS.
  destruct (eval_point_y_product t l m bp bt bl BT BL HPT HPL HTL HFP HT HFT HL HFL)
    as (m1 & C1 & Y1 & T1 & L1 & PF1 & TF1 & LF1 & VY & BY & F1).
  pose proof (field_at_lframe m m1 bs 0 _ _ HS F1
    ltac:(intro pos;repeat split;try congruence;left;congruence)) as S1.
  pose proof (curve_keep_free _ m m1 bs 40 ltac:(lia) HFS F1
    ltac:(intro pos;repeat split;try congruence;left;congruence)) as SF1.
  destruct (eval_point_field_add true PointY (point_mul_words t l) s m1 bp bs HPS Y1 PF1 S1 SF1)
    as (m2 & C2 & Y2 & S2 & PF2 & SF2 & F2).
  pose proof (field_tight_scaled _ BY) as BY1.
  pose proof (field_tight_scaled _ BS) as BS1.
  pose proof (field_sum_scaled_bounds 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BY1 BS1) as BSum.
  destruct (eval_point_y_negate2 (field_sum_words (point_mul_words t l) s) m2 bp BSum Y2 PF2)
    as (mf & C3 & Y3 & PF3 & VN & BN & F3).
  assert (E2 : lframe (fun b _ => b<>bp /\ b<>bs) m1 m2).
  { eapply lframe_implies;[exact F2|]. intros b pos [NP NS] HV;split;[exact NS|left;exact NP]. }
  pose proof (field_at_lframe m1 m2 bt 0 _ _ T1 E2 ltac:(intro pos;split;congruence)) as T2.
  pose proof (field_at_lframe m1 m2 bl 0 _ _ L1 E2 ltac:(intro pos;split;congruence)) as L2.
  pose proof (curve_keep_free _ m1 m2 bt 40 ltac:(lia) TF1 E2 ltac:(intro pos;split;congruence)) as TF2.
  pose proof (curve_keep_free _ m1 m2 bl 40 ltac:(lia) LF1 E2 ltac:(intro pos;split;congruence)) as LF2.
  pose proof (field_at_lframe m2 mf bt 0 _ _ T2 F3 ltac:(intro pos;left;congruence)) as T3.
  pose proof (field_at_lframe m2 mf bl 0 _ _ L2 F3 ltac:(intro pos;left;congruence)) as L3.
  pose proof (field_at_lframe m2 mf bs 0 _ _ S2 F3 ltac:(intro pos;left;congruence)) as S3.
  pose proof (curve_keep_free _ m2 mf bt 40 ltac:(lia) TF2 F3 ltac:(intro pos;left;congruence)) as TF3.
  pose proof (curve_keep_free _ m2 mf bl 40 ltac:(lia) LF2 F3 ltac:(intro pos;left;congruence)) as LF3.
  pose proof (curve_keep_free _ m2 mf bs 40 ltac:(lia) SF2 F3 ltac:(intro pos;left;congruence)) as SF3.
  assert (VS : radix_value (field_sum_words (point_mul_words t l) s)=radix_value (point_mul_words t l)+radix_value s).
  { apply field_sum_exact_value;exact (field_sum_scaled_no_overflow 1 1 _ _ ltac:(lia) ltac:(lia) ltac:(lia) BY1 BS1). }
  rewrite VS in VN.
  exists m1,m2,mf;split;[exact C1|];split;[exact C2|];split;[exact C3|].
  split;[exact Y3|];split;[exact T3|];split;[exact L3|];split;[exact S3|].
  split;[exact PF3|];split;[exact TF3|];split;[exact LF3|];split;[exact SF3|];split;[exact BN|].
  split;[unfold double_y_words;rewrite VN;ring|].
  eapply lframe_trans.
  - eapply lframe_implies;[exact F1|]. intros b pos (NT & NL & NS & NP) HV;repeat split;assumption.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact F2|]. intros b pos (NT & NL & NS & NP) HV;split;assumption.
    + eapply lframe_implies;[exact F3|]. intros b pos (NT & NL & NS & NP) HV;exact NP.
Qed.
