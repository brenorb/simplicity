(** Reuse the selected X/Y/Z square proofs on one owned 128-byte point.
    A prefix permission view is restored to full ownership by precise framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_state C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_point_write_run C.jet_secp_curve_square C.jet_secp_curve_square_caller.
Require Import C.jet_secp_curve_frame C.jet_secp_point_square_z.
Require Import C.jet_secp_square_numeric C.jet_secp_square_columns C.jet_secp_square_separate_numeric.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_multiply_checkpoint_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition point_square_coordinate_frame k (bout bin b : block) (pos : Z) :=
  ~((b=bout /\ 0<=pos<40) \/
    (b=bin /\ point_coordinate_offset k<=pos<point_coordinate_offset k+40)).

Lemma eval_point_square_xy_storage y rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (curve_square_offset y) (words5 rho) ->
  Mem.range_perm m bin 0 128 Cur Freeable -> bout<>bin ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (curve_square_offset y))] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin (curve_square_offset y) (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
    lframe (fun b pos => ~((b=bout /\ 0<=pos<40) \/
      (b=bin /\ curve_square_offset y<=pos<curve_square_offset y+40))) m mf.
Proof.
  intros HB HO HI HF HNe.
  assert (HF88 : Mem.range_perm m bin 0 88 Cur Freeable) by (intros pos HP;apply HF;lia).
  destruct (eval_curve_square_from_storage y rho m bout bin HB HO HI HF88 HNe)
    as (mf & HC & FO & FOF & FI & FIF88 & HV & HBounds & HL).
  assert (HValid : Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (HF 0);lia).
  assert (FIF : Mem.range_perm mf bin 0 128 Cur Freeable).
  { intros pos HP. destruct (Z_lt_ge_dec pos 88).
    - apply FIF88;lia.
    - apply (proj1 (proj2 HL));[exact HValid| |apply HF;exact HP].
      intro HFoot. destruct (curve_square_foot y bout bin bin pos HFoot) as [[HE _]|[_ HR]].
      + congruence.
      + destruct y;cbn [curve_square_offset] in HR;lia. }
  exists mf. split;[exact HC|]. split;[exact FO|]. split;[exact FOF|].
  split;[exact FI|]. split;[exact FIF|].
  eapply lframe_implies;[exact HL|]. intros b pos HOutside HVB HFoot.
  apply HOutside;exact (curve_square_foot y bout bin b pos HFoot).
Qed.

Theorem eval_point_square_coordinate k rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (point_coordinate_offset k) (words5 rho) ->
  Mem.range_perm m bin 0 128 Cur Freeable -> bout<>bin ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin (point_coordinate_offset k) (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
    radix_value (square_words rho) mod field_prime = (radix_value rho*radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\
    (forall i, (i<5)%nat -> 0<=Int64.unsigned (square_words rho i)<
      if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
    lframe (point_square_coordinate_frame k bout bin) m mf.
Proof.
  intros HB HO HI HF HNe.
  assert (HR : exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin (point_coordinate_offset k) (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
    lframe (point_square_coordinate_frame k bout bin) m mf).
  { destruct k.
    - exact (eval_point_square_xy_storage false rho m bout bin HB HO HI HF HNe).
    - exact (eval_point_square_xy_storage true rho m bout bin HB HO HI HF HNe).
    - destruct (eval_point_square_z_from_storage rho m bout bin HB HO HI HF HNe)
        as (mf & HC & FO & FOF & FI & FIF & HV & HBounds & HL).
      exists mf. split;[exact HC|]. split;[exact FO|]. split;[exact FOF|].
      split;[exact FI|]. split;[exact FIF|]. eapply lframe_implies;[exact HL|].
      intros b pos HOutside HVB HFoot. apply HOutside;exact (point_square_z_foot bout bin b pos HFoot). }
  destruct HR as (mf & HC & FO & FOF & FI & FIF & HL).
  exists mf. split;[exact HC|]. split;[exact FO|]. split;[exact FOF|].
  split;[exact FI|]. split;[exact FIF|]. split;[apply square_output_numeric;exact HB|].
  split;[apply square_result_reusable;exact HB|].
  split;[apply square_output_bounds;exact HB|exact HL].
Qed.
