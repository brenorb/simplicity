(** Remaining ten original arithmetic calls of distinct-source doubling.
    Every call is derived from storage and bounds, using the shared checked
    accumulation and Y-tail proofs. Source coordinates and flag bytes survive. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_double_separate_middle
 C.jet_secp_double_statements C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_secp_double_middle C.jet_secp_double_l_scale C.jet_secp_double_accumulate
 C.jet_secp_double_y_tail C.jet_secp_double_all_calls C.jet_secp_double_prefix
 C.jet_secp_field_sum_bounds C.jet_secp_field_mul_small C.jet_secp_square_columns
 C.jet_secp_square_numeric C.jet_secp_point_mul_storage C.jet_secp_point_write_run
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words double_l_words double_t_words double_y_words.

Definition double_separate_tail := statement_sequence
 (skipn 5 (fst (split_statement_last double_arithmetic_body)))
 (snd (split_statement_last double_arithmetic_body)).
Definition double_separate_frame (br ba bs bl bt b:block) (pos:Z) :=
 b<>bs /\ b<>bl /\ b<>bt /\ (b<>br \/ pos<0 \/ 120<=pos) /\ (b<>ba \/ pos<0 \/ 120<=pos).

Local Ltac tail_args HA HR := first [apply eval_Enil |
 eapply eval_Econs;
  [first [apply eval_curve_local;reflexivity |
    apply eval_double_point_address;[cbn [In];tauto|first [exact HA|exact HR]] | constructor]
  |reflexivity|tail_args HA HR]].
Local Ltac tail_call HA HR Call := lazymatch type of Call with
 | Clight2.eval_funcall _ _ _ ?args _ _ ?value =>
 eapply exec_curve_call with (vargs:=args) (v:=value);
  [unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]) |
   reflexivity | tail_args HA HR | exact Call] end.

Local Ltac keep_after_acc Field Frame :=
 eapply field_at_lframe;[exact Field|exact Frame|];intros pos;
 unfold double_accum_frame;repeat split;try congruence;left;congruence.
Local Ltac keep_after_y Field Frame :=
 eapply field_at_lframe;[exact Field|exact Frame|];intros pos;
 unfold double_y_tail_frame;repeat split;try congruence;left;congruence.

Theorem exec_double_separate_tail le x y z m br ba bs bl bt :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 square_input_bounds x -> mul_small_input_bounds (square_words y) ->
 square_input_bounds (double_l_words (square_words x)) ->
 square_input_bounds (double_output_z_words y z) ->
 br<>ba -> br<>bs -> br<>bl -> br<>bt ->
 ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 fe_at m br 80 (words5 (double_output_z_words y z)) ->
 fe_at m bs 0 (words5 (square_words y)) ->
 fe_at m bl 0 (words5 (double_l_words (square_words x))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bl 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m double_separate_tail E0 le mf Out_normal /\
 fe_at mf br 0 (words5 (double_output_x_words x y)) /\
 fe_at mf br 40 (words5 (double_output_y_words x y)) /\
 fe_at mf br 80 (words5 (double_output_z_words y z)) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds (double_output_x_words x y) /\
 square_input_bounds (double_output_y_words x y) /\
 square_input_bounds (double_output_z_words y z) /\
 lframe (double_separate_frame br ba bs bl bt) m mf.
Proof.
 intros HA HR BX BS BL BZ RA RS RL RT AS AL AT SL ST LT X Y ZAt RZ S L RF AF SF LF TF.
 destruct (double_separate_middle_calls x (square_words y) (double_l_words (square_words x))
   m br ba bs bl bt BX BS BL RA RS RL RT AS AL AT SL ST LT X S L RF AF SF LF TF)
  as (m6 & m7 & m8 & C6 & C7 & C8 & RX8 & AX8 & S8 & L8 & T8 &
      RF8 & AF8 & SF8 & LF8 & TF8 & BRX8 & BT8 & F58).
 assert (AY8:fe_at m8 ba 40 (words5 y)).
 { eapply curve_keep_field_range;[reflexivity|exact Y|exact F58|].
   intros pos Range;unfold double_separate_middle_frame;repeat split;try congruence;
     [right;right;lia|left;congruence]. }
 assert (AZ8:fe_at m8 ba 80 (words5 z)).
 { eapply curve_keep_field_range;[reflexivity|exact ZAt|exact F58|].
   intros pos Range;unfold double_separate_middle_frame;repeat split;try congruence;
     [right;right;lia|left;congruence]. }
 assert (RZ8:fe_at m8 br 80 (words5 (double_output_z_words y z))).
 { eapply curve_keep_field_range;[reflexivity|exact RZ|exact F58|].
   intros pos Range;unfold double_separate_middle_frame;repeat split;try congruence;
     [left;congruence|right;right;lia]. }
 assert (BSL:square_input_bounds (square_words y)) by
   exact (field_scaled_loose 1 _ ltac:(lia) (field_tight_scaled _ BS)).
 destruct (double_accumulate_calls _ _ _ m8 br bt bs BRX8 BT8 BSL RT RS (not_eq_sym ST)
   RX8 T8 S8 RF8 TF8 SF8)
  as (m9 & m10 & m11 & m12 & C9 & C10 & C11 & C12 & RX12 & T12 & S12 & RF12 & TF12 & SF12 &
      BRX12 & BT12 & BS12 & VX12 & VT12 & VS12 & F812).
 assert (AX12:fe_at m12 ba 0 (words5 x)) by (keep_after_acc AX8 F812).
 assert (AY12:fe_at m12 ba 40 (words5 y)) by (keep_after_acc AY8 F812).
 assert (AZ12:fe_at m12 ba 80 (words5 z)) by (keep_after_acc AZ8 F812).
 assert (L12:fe_at m12 bl 0 (words5 (double_l_words (square_words x)))) by (keep_after_acc L8 F812).
 assert (RZ12:fe_at m12 br 80 (words5 (double_output_z_words y z))).
 { eapply curve_keep_field_range;[reflexivity|exact RZ8|exact F812|].
   intros pos Range;unfold double_accum_frame;repeat split;try congruence;right;right;lia. }
 assert (AF12:Mem.range_perm m12 ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AF8|exact F812|].
   intros pos;unfold double_accum_frame;repeat split;try congruence;left;congruence. }
 assert (LF12:Mem.range_perm m12 bl 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact LF8|exact F812|].
   intros pos;unfold double_accum_frame;repeat split;try congruence;left;congruence. }
 destruct (double_y_tail_calls _ _ _ m12 br bt bl bs
   (field_scaled_loose 4 _ ltac:(lia) BT12) BL BS12 RT RL RS (not_eq_sym LT) (not_eq_sym ST) (not_eq_sym SL)
   T12 L12 S12 RF12 TF12 LF12 SF12)
  as (m13 & m14 & mf & C13 & C14 & C15 & RYF & TFinal & LFinal & SFinal &
      RFF & TFF & LFF & SFF & BYF & VYF & F12F).
 assert (RXF:fe_at mf br 0 (words5 (double_output_x_words x y))).
 { eapply curve_keep_field_range;[reflexivity|exact RX12|exact F12F|].
   intros pos Range;unfold double_y_tail_frame;repeat split;try congruence;right;left;lia. }
 assert (RZF:fe_at mf br 80 (words5 (double_output_z_words y z))).
 { eapply curve_keep_field_range;[reflexivity|exact RZ12|exact F12F|].
   intros pos Range;unfold double_y_tail_frame;repeat split;try congruence;right;right;lia. }
 assert (AXF:fe_at mf ba 0 (words5 x)) by (keep_after_y AX12 F12F).
 assert (AYF:fe_at mf ba 40 (words5 y)) by (keep_after_y AY12 F12F).
 assert (AZF:fe_at mf ba 80 (words5 z)) by (keep_after_y AZ12 F12F).
 assert (AFF:Mem.range_perm mf ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AF12|exact F12F|].
   intros pos;unfold double_y_tail_frame;repeat split;try congruence;left;congruence. }
 exists mf;split.
 - unfold double_separate_tail,double_arithmetic_body;cbn [split_statement_last fst snd skipn fold_right statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m6) (le1:=le);[tail_call HA HR C6|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m7) (le1:=le);[tail_call HA HR C7|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m8) (le1:=le);[tail_call HA HR C8|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m9) (le1:=le);[tail_call HA HR C9|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m10) (le1:=le);[tail_call HA HR C10|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m11) (le1:=le);[tail_call HA HR C11|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m12) (le1:=le);[tail_call HA HR C12|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m13) (le1:=le);[tail_call HA HR C13|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m14) (le1:=le);[tail_call HA HR C14|].
   tail_call HA HR C15.
 - split;[exact RXF|];split;[exact RYF|];split;[exact RZF|];
   split;[exact AXF|];split;[exact AYF|];split;[exact AZF|];split;[exact RFF|];
   split;[exact AFF|];split;[exact SFF|];split;[exact LFF|];split;[exact TFF|];
   split;[exact (field_scaled_loose 3 _ ltac:(lia) BRX12)|];split;[exact BYF|];split;[exact BZ|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact F58|].
     intros b pos (NS & NL & NT & NR & NA) Valid;unfold double_separate_middle_frame;
       repeat split;try assumption;
       [destruct NA as [NA|[NA|NA]]|destruct NR as [NR|[NR|NR]]];intuition lia.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact F812|].
       intros b pos (NS & NL & NT & NR & NA) Valid;unfold double_accum_frame;
         repeat split;try assumption;destruct NR as [NR|[NR|NR]];intuition lia.
     * eapply lframe_implies;[exact F12F|].
       intros b pos (NS & NL & NT & NR & NA) Valid;unfold double_y_tail_frame;
         repeat split;try assumption;destruct NR as [NR|[NR|NR]];intuition lia.
Qed.
