(** The unchanged SWU suffix reads the stored low bit, also when a generator
    digest was rejected by set_b32. Preserve that raw parity in the result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_fns C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
  C.jet_secp_field_cmov C.jet_secp_swu_parity_fields C.jet_secp_swu_parity
  C.jet_secp_field_odd_words C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge C.jet_secp_multiply_input_input
  C.jet_secp_canonical_odd C.jet_secp_canonical_normalize C.jet_clight_internal_preserve.
Require Import C.jet_secp_rescale_literal C.jet_secp_gej_negate_literal C.jet_secp_negate_literal_contract
  C.jet_secp_swu_literal C.jet_secp_swu_literal_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_words_parity_temps input le := PTree.set _t'3 (Vint (cmov_int (field_words_odd input))) le.
Definition swu_words_parity input w := if field_words_odd input then negate_sep_words w else w.
Definition swu_words_literal_output input t := if field_words_odd input
  then @literal_ge_negate Alg.CoreFunSem (swu_selected_candidate t) else swu_selected_candidate t.

Lemma swu_reader_words_odd t : field_words_odd (square_reader_rho t)=swu_input_odd t.
Proof.
  unfold field_words_odd,square_reader_rho.
  change (Z.testbit (Int64.unsigned (Int64.repr (normalized_value t mod 2^52))) 0=swu_input_odd t).
  rewrite Int64.unsigned_repr by
    (pose proof (Z.mod_pos_bound (normalized_value t) (2^52) ltac:(lia));
      change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite Z.mod_pow2_bits_low by lia.
  unfold swu_input_odd;rewrite canonical_fe_is_odd_numeric;reflexivity.
Qed.

Lemma swu_words_parity_matches_literal input x y : mul_small_input_bounds y ->
  (rescale_field_output x,rescale_field_output (swu_words_parity input y))=
  if field_words_odd input then @literal_ge_negate Alg.CoreFunSem (rescale_field_output x,rescale_field_output y)
  else (rescale_field_output x,rescale_field_output y).
Proof.
  intro Bounds;unfold swu_words_parity;destruct (field_words_odd input).
  - change ((rescale_field_output x,rescale_field_output (negate_sep_words y))=
      (@canonical_fe_normalize Alg.CoreFunSem (rescale_field_output x),
       @literal_fe_negate Alg.CoreFunSem (rescale_field_output y))).
    rewrite swu_serialized_field_normalized,swu_negated_field_output by exact Bounds;reflexivity.
  - reflexivity.
Qed.
Lemma swu_words_parity_reader t w : swu_words_parity (square_reader_rho t) w=swu_parity_words t w.
Proof. unfold swu_words_parity,swu_parity_words;rewrite swu_reader_words_odd;reflexivity. Qed.
Lemma swu_words_parity_reader_temps t le :
  swu_words_parity_temps (square_reader_rho t) le=swu_parity_temps t le.
Proof. unfold swu_words_parity_temps,swu_parity_temps;rewrite swu_reader_words_odd;reflexivity. Qed.
Lemma swu_words_literal_output_reader t :
  swu_words_literal_output (square_reader_rho t) t=@literal_swu Alg.CoreFunSem t.
Proof. unfold swu_words_literal_output;rewrite swu_reader_words_odd,swu_literal_selected_step;reflexivity. Qed.

Lemma exec_swu_words_odd_call input e le m mf bi :
  e!_secp256k1_fe_is_odd=None -> le!_t=Some (Vptr bi Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
    [Vptr bi Ptrofs.zero] E0 mf (Vint (cmov_int (field_words_odd input))) ->
  Clight2.exec_stmt secp_ge e le m swu_parity_odd_call E0 (swu_words_parity_temps input le) mf Out_normal.
Proof.
  intros Fun T Call;unfold swu_parity_odd_call,swu_words_parity_temps;eapply exec_curve_call with
    (vargs:=[Vptr bi Ptrofs.zero]) (v:=Vint (cmov_int (field_words_odd input))).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_Etempvar;exact T|reflexivity|constructor].
  - exact Call.
Qed.
Lemma exec_swu_words_cmov_call input e le m mf bt bp :
  e!_secp256k1_fe_cmov=None -> e!_tmp=Some (bt,curve_fe_type) -> le!_ge=Some (Vptr bp Ptrofs.zero) ->
  le!_t'3=Some (Vint (cmov_int (field_words_odd input))) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_cmov)
    [Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int (field_words_odd input))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m swu_parity_cmov_call E0 le mf Out_normal.
Proof.
  intros Fun Temp Ge Flag Call;unfold swu_parity_cmov_call;eapply exec_curve_call with
    (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr bt Ptrofs.zero;Vint (cmov_int (field_words_odd input))]) (v:=Vundef).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs;[apply eval_swu_ge_y;exact Ge|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;exact Temp|reflexivity|].
    eapply eval_Econs;[apply eval_Etempvar;exact Flag|reflexivity|constructor].
  - exact Call.
Qed.

Theorem exec_swu_words_parity input w e le m bi bt bp :
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_is_odd=None -> e!_secp256k1_fe_cmov=None ->
  e!_tmp=Some (bt,curve_fe_type) -> le!_ge=Some (Vptr bp Ptrofs.zero) -> le!_t=Some (Vptr bi Ptrofs.zero) ->
  NoDup [bi;bt;bp] -> mul_small_input_bounds w ->
  fe_at m bi 0 (words5 input) -> fe_at m bp 40 (words5 w) ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m swu_parity_tail E0 (swu_words_parity_temps input le) mf Out_normal /\
  fe_at mf bp 40 (words5 (swu_words_parity input w)) /\
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
  assert (Input1:fe_at m1 bi 0 (words5 input)).
  { eapply curve_keep_field_range;[reflexivity|exact Input|exact FN|intros;split;[exact IT|left;exact IP]]. }
  assert (FI1:Mem.range_perm m1 bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FI|exact FN|intros;split;[exact IT|left;exact IP]]. }
  destruct (eval_field_odd_words input m1 bi Input1 FI1) as (m2 & Odd & FI2 & FO & RO).
  assert (Temp2:fe_at m2 bt 0 (words5 (negate_sep_words w))) by
    (eapply curve_keep_field_range;[reflexivity|exact Temp1|exact FO|intros;congruence]).
  assert (Y2:fe_at m2 bp 40 (words5 w)) by
    (eapply curve_keep_field_range;[reflexivity|exact Y1|exact FO|intros;congruence]).
  assert (FT2:Mem.range_perm m2 bt 0 40 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FT1|exact FO|intros;congruence]).
  assert (FP2:Mem.range_perm m2 bp 0 88 Cur Freeable) by
    (eapply curve_keep_free;[lia|exact FP1|exact FO|intros;congruence]).
  destruct (eval_swu_cmov_y (field_words_odd input) w (negate_sep_words w) m2 bp bt
    ltac:(congruence) Y2 Temp2 FP2 FT2)
    as (mf & Move & YF & TF & FPF & FTF & FM & RM).
  assert (FIF:Mem.range_perm mf bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FI2|exact FM|intros;split;[exact IT|left;exact IP]]. }
  assert (GeFinal:(swu_words_parity_temps input le)!_ge=Some (Vptr bp Ptrofs.zero)) by
    (unfold swu_words_parity_temps;rewrite PTree.gso by discriminate;exact Ge).
  exists mf;split.
  - unfold swu_parity_tail.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le);
      [eapply exec_swu_parity_neg_call;eassumption|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=swu_words_parity_temps input le).
    + eapply exec_swu_words_odd_call;eassumption.
    + eapply exec_swu_words_cmov_call;[exact EC|exact ET|exact GeFinal| |exact Move].
      unfold swu_words_parity_temps;apply PTree.gss.
  - split;[exact YF|];split;[exact FIF|];split;[exact FTF|];split;[exact FPF|];split.
    + eapply lframe_trans with (m2:=m1).
      * eapply lframe_implies;[exact FN|];intros b pos [NI Rest] Valid;exact Rest.
      * eapply lframe_trans with (m2:=m2).
        { eapply lframe_implies;[exact FO|];intros b pos [NI Rest] Valid;exact NI. }
        eapply lframe_implies;[exact FM|];intros b pos [NI Rest] Valid;exact Rest.
    + eapply preserved_trans;[exact RN|];eapply preserved_trans;[exact RO|exact RM].
Qed.
