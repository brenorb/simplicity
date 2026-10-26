(** Calls six through eight of the original doubling with a distinct result.
    The X source and X destination are different allocations; no source copy
    or in-place substitute is inserted. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math
 C.jet_secp_point_write_run C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_field_negate_separate C.jet_secp_field_point_multiply C.jet_secp_square_point_x
 C.jet_secp_field_mul_small C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_gej_curve_coordinate C.jet_secp_point_square_coordinate
 C.jet_secp_point_mul_storage C.jet_secp_double_middle
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words negate_sep_words.

Definition double_separate_middle_frame (br ba bs bl bt b:block) (pos:Z) :=
 b<>bs /\ b<>bl /\ b<>bt /\ (b<>ba \/ pos<0 \/ 40<=pos) /\ (b<>br \/ pos<0 \/ 40<=pos).

Theorem double_separate_middle_calls x s l m br ba bs bl bt :
 square_input_bounds x -> mul_small_input_bounds s -> square_input_bounds l ->
 br<>ba -> br<>bs -> br<>bl -> br<>bt ->
 ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
 fe_at m ba 0 (words5 x) -> fe_at m bs 0 (words5 s) -> fe_at m bl 0 (words5 l) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists m1 m2 mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
  [Vptr bt Ptrofs.zero;Vptr bs Ptrofs.zero;Vint Int.one] E0 m1 Vundef /\
 Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
  [Vptr bt Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 m2 Vundef /\
 Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_sqr)
  [Vptr br Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (square_words l)) /\ fe_at mf ba 0 (words5 x) /\
 fe_at mf bs 0 (words5 s) /\ fe_at mf bl 0 (words5 l) /\
 fe_at mf bt 0 (words5 (double_t_words x s)) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 mul_small_input_bounds (square_words l) /\ mul_small_input_bounds (double_t_words x s) /\
 lframe (double_separate_middle_frame br ba bs bl bt) m mf.
Proof.
 intros BX BS BL RA RS RL RT AS AL AT SL ST LT X S L RF AF SF LF TF.
 destruct (eval_negate_sep_from_storage s m bt bs BS (not_eq_sym ST) TF S SF)
  as (m1 & C1 & T1 & S1 & TF1 & SF1 & VN & BN & F1).
 assert (X1:fe_at m1 ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact F1|];intros;split;congruence).
 assert (L1:fe_at m1 bl 0 (words5 l)) by
  (eapply field_at_lframe;[exact L|exact F1|];intros;split;congruence).
 assert (RF1:Mem.range_perm m1 br 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact RF|exact F1|];intros;split;congruence).
 assert (AF1:Mem.range_perm m1 ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AF|exact F1|];intros;split;congruence).
 assert (LF1:Mem.range_perm m1 bl 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact LF|exact F1|];intros;split;congruence).
 destruct (eval_field_point_mul_numeric PointX (negate_sep_words s) x m1 bt ba BN BX
   (not_eq_sym AT) T1 TF1 X1 AF1)
  as (m2 & C2 & T2 & TF2 & X2 & AF2 & VT & BT2 & BTT & F2).
 pose proof (coordinate_frame_blocks PointX bt ba m1 m2 F2) as E2.
 assert (S2:fe_at m2 bs 0 (words5 s)) by
  (eapply field_at_lframe;[exact S1|exact E2|];intros;split;congruence).
 assert (L2:fe_at m2 bl 0 (words5 l)) by
  (eapply field_at_lframe;[exact L1|exact E2|];intros;split;congruence).
 assert (RF2:Mem.range_perm m2 br 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact RF1|exact E2|];intros;split;congruence).
 assert (SF2:Mem.range_perm m2 bs 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact SF1|exact E2|];intros;split;congruence).
 assert (LF2:Mem.range_perm m2 bl 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact LF1|exact E2|];intros;split;congruence).
 destruct (eval_square_point_x l m2 br bl BL RF2 L2 LF2 RL)
  as (mf & C3 & R3 & RF3 & L3 & LF3 & VX & BX3 & BTX & F3).
 assert (E3:lframe (fun b _=>b<>br /\ b<>bl) m2 mf).
 { eapply lframe_implies;[exact F3|];intros b pos [NR NL] Valid.
   unfold square_two_ranges;intros [[Same Range]|[Same Range]];congruence. }
 assert (X3:fe_at mf ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact X2|exact E3|];intros;split;congruence).
 assert (S3:fe_at mf bs 0 (words5 s)) by
  (eapply field_at_lframe;[exact S2|exact E3|];intros;split;congruence).
 assert (T3:fe_at mf bt 0 (words5 (double_t_words x s))) by
  (eapply field_at_lframe;[exact T2|exact E3|];intros;split;congruence).
 assert (AF3:Mem.range_perm mf ba 0 128 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact AF2|exact E3|];intros;split;congruence).
 assert (SF3:Mem.range_perm mf bs 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact SF2|exact E3|];intros;split;congruence).
 assert (TF3:Mem.range_perm mf bt 0 40 Cur Freeable) by
  (eapply curve_keep_free;[lia|exact TF2|exact E3|];intros;split;congruence).
 exists m1,m2,mf;split;[exact C1|];split;[exact C2|];split;[exact C3|];
  split;[exact R3|];split;[exact X3|];split;[exact S3|];split;[exact L3|];
  split;[exact T3|];split;[exact RF3|];split;[exact AF3|];split;[exact SF3|];
  split;[exact LF3|];split;[exact TF3|];split;[exact BTX|];split;[exact BTT|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact F1|].
   intros b pos (NS & NL & NT & NA & NR) Valid;split;assumption.
 - eapply lframe_trans.
   + eapply lframe_implies;[exact F2|].
     intros b pos (NS & NL & NT & NA & NR) Valid.
     unfold point_square_coordinate_frame;intros [[Same Range]|[Same Range]];
      [congruence|subst b;destruct NA as [NA|[NA|NA]];
       cbn [point_coordinate_offset] in Range;intuition lia].
   + eapply lframe_implies;[exact F3|].
     intros b pos (NS & NL & NT & NA & NR) Valid.
     unfold square_two_ranges;intros [[Same Range]|[Same Range]];
      [subst b;destruct NR as [NR|[NR|NR]];intuition lia|congruence].
Qed.
