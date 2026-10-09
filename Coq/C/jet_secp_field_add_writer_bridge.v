(** Reuse the actual wide writer interface for the actual C add outputs.
    The modular value equality below is representation support, not a
    replacement for the literal carry/add/normalize512 specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
Require Import Simplicity.Word.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_secp_fe_nv.
Require Import C.jet_secp_field_add_values C.jet_secp_field_add_storage.
Require Import C.jet_secp_field_add_numeric C.jet_secp_local_regions.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_negate_writer_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma add_writer_initial_rep rho rc m b :
  fe_at m b 0 (add_values rho) ->
  Mem.range_perm m b 0 40 Cur Freeable ->
  rep (wide_fe_rho (add_value rho 0) (add_value rho 1)
    (add_value rho 2) (add_value rho 3) (add_value rho 4) rc)
    [(b,0)] local_write_initial_regs m.
Proof. apply wide_field_initial_rep. Qed.

Lemma add_writer_limb_bounds rho :
  (forall n, (n < 5)%nat ->
    Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1) ->
  forall n, (n < 5)%nat -> Int64.unsigned (add_value rho n) <= 2 ^ 60.
Proof.
  intros H n Hn. destruct (H n Hn) as [HA HB].
  pose proof (add_value_wide_bound rho n HA HB). lia.
Qed.

Lemma add_writer_output_sum rho :
  (forall n, (n < 5)%nat ->
    Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1) ->
  @toZ (WordToZ 8)
    (wide_fe_output (add_value rho 0) (add_value rho 1)
      (add_value rho 2) (add_value rho 3) (add_value rho 4)) =
    (field_input_value rho 1 + field_input_value rho 6) mod C.jet_secp_fe_math.feP.
Proof.
  intro H. rewrite wide_fe_output_value, field_add_values_sum by exact H.
  reflexivity.
Qed.
Print Assumptions add_writer_initial_rep.
Print Assumptions add_writer_limb_bounds.
Print Assumptions add_writer_output_sum.
