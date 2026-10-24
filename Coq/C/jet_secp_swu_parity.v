(** The original final SWU negation/oddness/move suffix. The oddness call
    uses the real reader's normalized representation, not mere equality
    modulo the odd prime. Every C call executes in both parity cases. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fns C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_field_predicates C.jet_secp_field_mul_small
  C.jet_secp_field_negate_separate C.jet_secp_field_cmov C.jet_secp_swu_parity_fields
  C.jet_secp_swu_select_exec C.jet_secp_swu_literal_bridge C.jet_secp_swu_literal
  C.jet_secp_canonical_odd C.jet_secp_canonical_normalize C.jet_secp_square_spec_bridge
  C.jet_secp_multiply_input_input C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_closed_helpers
  C.jet_secp_field_add_initial C.jet_secp_b32_exec C.jet_secp_write_fe_numeric
  C.jet_secp_double_coordinate_numeric C.jet_secp_rescale_literal C.jet_secp_gej_negate_literal
  C.jet_secp_negate_literal_contract C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_odd canonical_fe_normalize rescale_field_output literal_fe_negate.

Definition swu_input_odd (t:Ty.tySem (Word 8)) := Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem t).
Definition swu_parity_temps t le := PTree.set _t'3 (Vint (cmov_int (swu_input_odd t))) le.
Definition swu_parity_words t w := if swu_input_odd t then negate_sep_words w else w.
Definition swu_ge_y_address := Eaddrof
  (Efield (Ederef (Etempvar _ge (tptr curve_ge_type)) curve_ge_type) _y curve_fe_type) (tptr curve_fe_type).
Definition swu_construct_call := curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
  [Etempvar _ge (tptr curve_ge_type);curve_local_address _x1;curve_local_address _y1].
Definition swu_parity_neg_call := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
  [curve_local_address _tmp;swu_ge_y_address;Econst_int Int.one tint].
Definition swu_parity_odd_call := curve_call _secp256k1_fe_is_odd f_secp256k1_fe_is_odd (Some _t'3)
  [Etempvar _t (tptr curve_fe_type)].
Definition swu_parity_cmov_call := curve_call _secp256k1_fe_cmov f_secp256k1_fe_cmov None
  [swu_ge_y_address;curve_local_address _tmp;Etempvar _t'3 tint].
Definition swu_parity_tail := Ssequence swu_parity_neg_call (Ssequence swu_parity_odd_call swu_parity_cmov_call).
Lemma swu_parity_source : swu_after_select=Ssequence swu_construct_call swu_parity_tail.
Proof. reflexivity. Qed.
Lemma eval_swu_ge_y e le m bp : le!_ge=Some (Vptr bp Ptrofs.zero) ->
  eval_expr secp_ge e le m swu_ge_y_address (Vptr bp (Ptrofs.repr 40)).
Proof.
  intro Ge;destruct (curve_affine_layout _y 40 ltac:(right;left;reflexivity)) as (co & CO & Offset).
  unfold swu_ge_y_address;apply eval_Eaddrof;rewrite <-(Ptrofs.add_zero_l (Ptrofs.repr 40)).
  eapply eval_Efield_struct with (co:=co) (delta:=40).
  - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact Ge|apply deref_loc_copy;reflexivity].
  - reflexivity.
  - exact CO.
  - exact Offset.
Qed.
Lemma exec_swu_parity_neg_call e le m mf bt bp :
  e!_secp256k1_fe_negate=None -> e!_tmp=Some (bt,curve_fe_type) -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr bt Ptrofs.zero;Vptr bp (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_parity_neg_call E0 le mf Out_normal.
Proof.
  intros Fun Temp Ge Call;unfold swu_parity_neg_call;eapply exec_curve_call with
    (vargs:=[Vptr bt Ptrofs.zero;Vptr bp (Ptrofs.repr 40);Vint Int.one]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_curve_local;exact Temp|reflexivity|].
    eapply eval_Econs;[apply eval_swu_ge_y;exact Ge|reflexivity|].
    eapply eval_Econs;[constructor|reflexivity|constructor].
  - exact Call.
Qed.

Lemma exec_swu_parity_odd_call t e le m mf bi :
  e!_secp256k1_fe_is_odd=None -> le!_t=Some (Vptr bi Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
    [Vptr bi Ptrofs.zero] E0 mf (Vint (cmov_int (swu_input_odd t))) ->
  Clight2.exec_stmt secp_ge e le m swu_parity_odd_call E0 (swu_parity_temps t le) mf Out_normal.
Proof.
  intros Fun T Call;unfold swu_parity_odd_call,swu_parity_temps;eapply exec_curve_call with
    (vargs:=[Vptr bi Ptrofs.zero]) (v:=Vint (cmov_int (swu_input_odd t))).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_Etempvar;exact T|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_parity_cmov_call t e le m mf bt bp :
  e!_secp256k1_fe_cmov=None -> e!_tmp=Some (bt,curve_fe_type) -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  le!_t'3=Some (Vint (cmov_int (swu_input_odd t))) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int (swu_input_odd t))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_parity_cmov_call E0 le mf Out_normal.
Proof.
  intros Fun Temp Ge Flag Call;unfold swu_parity_cmov_call;eapply exec_curve_call with
    (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int (swu_input_odd t))]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_swu_ge_y;exact Ge|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact Temp|reflexivity|].
    eapply eval_Econs;[apply eval_Etempvar;exact Flag|reflexivity|constructor].
  - exact Call.
Qed.

Definition swu_parity_frame (bi bt bp b:block) pos := b<>bi /\ swu_y_frame bt bp b pos.
Theorem exec_swu_parity t w e le m bi bt bp :
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_is_odd=None -> e!_secp256k1_fe_cmov=None ->
  e!_tmp=Some (bt,curve_fe_type) -> le!_ge=Some (Vptr bp Ptrofs.zero) -> le!_t=Some (Vptr bi Ptrofs.zero) ->
  NoDup [bi;bt;bp] -> mul_small_input_bounds w ->
  fe_at m bi 0 (words5 (square_reader_rho t)) -> fe_at m bp 40 (words5 w) ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_parity_tail E0 (swu_parity_temps t le) mf Out_normal /\
  fe_at mf bp 40 (words5 (swu_parity_words t w)) /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\
  lframe (swu_parity_frame bi bt bp) m mf /\ readonly_preserved m mf.
Proof.
  intros EN EO EC ET Ge T Sep Bounds Input Y FI FT FP.
  assert (Pairs:bi<>bt /\ bi<>bp /\ bt<>bp) by
    (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;intuition congruence).
  destruct Pairs as [IT [IP TP]].
  destruct (eval_swu_negate_y w m bt bp TP Bounds FT Y FP)
    as (m1 & Neg & Temp1 & Y1 & FT1 & FP1 & Value & NegBounds & FN & RN).
  assert (Input1:fe_at m1 bi 0 (words5 (square_reader_rho t))).
  { eapply curve_keep_field_range;[reflexivity|exact Input|exact FN|];
      intros;split;[exact IT|left;exact IP]. }
  assert (FI1:Mem.range_perm m1 bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FI|exact FN|];intros;split;[exact IT|left;exact IP]. }
  assert (OddInput:fe_at m1 bi 0 (map Int64.repr
    (fe_limbs_of (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem t))))).
  { exact Input1. }
  destruct (eval_field_odd_canonical m1 bi t OddInput FI1) as (m2 & Odd & FI2 & FO).
  change (Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_is_odd)
    [Vptr bi Ptrofs.zero] E0 m2 (Vint (cmov_int (swu_input_odd t)))) in Odd.
  assert (RO:readonly_preserved m1 m2) by
    (eapply (secp_closed_function_preserved f_secp256k1_fe_is_odd);[reflexivity|reflexivity|exact Odd]).
  assert (Temp2:fe_at m2 bt 0 (words5 (negate_sep_words w))) by
    (eapply curve_keep_field_range;[reflexivity|exact Temp1|exact FO|];intros;congruence).
  assert (Y2:fe_at m2 bp 40 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact Y1|exact FO|];intros;congruence).
  assert (FT2:Mem.range_perm m2 bt 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FT1|exact FO|];intros;congruence).
  assert (FP2:Mem.range_perm m2 bp 0 88 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FP1|exact FO|];intros;congruence).
  destruct (eval_swu_cmov_y (swu_input_odd t) w (negate_sep_words w) m2 bp bt
    ltac:(congruence) Y2 Temp2 FP2 FT2)
    as (mf & Move & YF & TF & FPF & FTF & FM & RM).
  assert (FIF:Mem.range_perm mf bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FI2|exact FM|];intros;split;[exact IT|left;exact IP]. }
  assert (GeFinal:(swu_parity_temps t le)!_ge=Some (Vptr bp Ptrofs.zero)) by
    (unfold swu_parity_temps;rewrite PTree.gso by discriminate;exact Ge).
  exists mf;split.
  - unfold swu_parity_tail.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);
      [eapply exec_swu_parity_neg_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=swu_parity_temps t le).
    + eapply exec_swu_parity_odd_call;eassumption.
    + eapply exec_swu_parity_cmov_call;[exact EC|exact ET|exact GeFinal| |exact Move].
      unfold swu_parity_temps;apply PTree.gss.
  - split;[exact YF|];split;[exact FIF|];split;[exact FTF|];split;[exact FPF|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact FN|];intros b pos [NI Rest] Valid;exact Rest.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact FO|];intros b pos [NI Rest] Valid;exact NI. }
        eapply lframe_implies;[exact FM|];intros b pos [NI Rest] Valid;exact Rest.
    + eapply preserved_trans;[exact RN|];eapply preserved_trans;[exact RO|exact RM].
Qed.

Lemma swu_negated_field_output w : mul_small_input_bounds w ->
  rescale_field_output (negate_sep_words w)=@literal_fe_negate Alg.CoreFunSem (rescale_field_output w).
Proof.
  intro Bounds;apply (toZ_injective (WordToZ 8)).
  rewrite rescale_field_output_value,field_prime_matches_normalizer.
  apply double_negate_sep_matches;[exact Bounds|].
  rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia).
  reflexivity.
Qed.
Lemma swu_serialized_field_normalized w :
  @canonical_fe_normalize Alg.CoreFunSem (rescale_field_output w)=rescale_field_output w.
Proof.
  apply (toZ_injective (WordToZ 8));rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
  rewrite !rescale_field_output_value,!field_prime_matches_normalizer.
  apply Z.mod_mod;unfold feP,feR;lia.
Qed.
Theorem swu_parity_matches_literal t x y : mul_small_input_bounds y ->
  (rescale_field_output x,rescale_field_output (swu_parity_words t y))=
  if swu_input_odd t then @literal_ge_negate Alg.CoreFunSem (rescale_field_output x,rescale_field_output y)
  else (rescale_field_output x,rescale_field_output y).
Proof.
  intro Bounds;unfold swu_parity_words;destruct (swu_input_odd t).
  - change ((rescale_field_output x,rescale_field_output (negate_sep_words y))=
      (@canonical_fe_normalize Alg.CoreFunSem (rescale_field_output x),
       @literal_fe_negate Alg.CoreFunSem (rescale_field_output y))).
    rewrite swu_serialized_field_normalized,swu_negated_field_output by exact Bounds;reflexivity.
  - reflexivity.
Qed.
Corollary swu_parity_of_selected_matches t x y : mul_small_input_bounds y ->
  (rescale_field_output x,rescale_field_output y)=swu_selected_candidate t ->
  (rescale_field_output x,rescale_field_output (swu_parity_words t y))=@literal_swu Alg.CoreFunSem t.
Proof.
  intros Bounds Selected;rewrite swu_literal_selected_step,(swu_parity_matches_literal t x y Bounds),Selected.
  reflexivity.
Qed.
