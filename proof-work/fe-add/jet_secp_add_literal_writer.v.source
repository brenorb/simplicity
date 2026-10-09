(** Compare actual add limb outputs with the literal canonical field program.
    Reader value/bound facts remain intermediate obligations to discharge
    from the public Word256-pair input frame. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word.
Require Import C.jet_toZ.
Require Import C.jet_secp_canonical_normalize C.jet_secp_fe_math.
Require Import C.jet_secp_field_add_values C.jet_secp_field_add_numeric.
Require Import C.jet_secp_field_add_writer_bridge C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma add_writer_literal_output rho (a b : Ty.tySem (Word 8)) :
  (forall n, (n < 5)%nat ->
    Int64.unsigned (rho (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (rho ((6 + n)%nat)) <= 2 ^ 52 - 1) ->
  field_input_value rho 1 = @toZ (WordToZ 8) a mod canonical_field_order ->
  field_input_value rho 6 = @toZ (WordToZ 8) b mod canonical_field_order ->
  wide_fe_output (add_value rho 0) (add_value rho 1)
    (add_value rho 2) (add_value rho 3) (add_value rho 4) =
  @literal_fe_add Alg.CoreFunSem (a,b).
Proof.
  intros HBounds HA HB. apply (toZ_injective (WordToZ 8)).
  rewrite add_writer_output_sum by exact HBounds.
  rewrite <- canonical_field_order_matches_limb_model, HA, HB, literal_fe_add_numeric.
  symmetry. apply Z.add_mod.
  pose proof canonical_field_order_range. lia.
Qed.
Print Assumptions add_writer_literal_output.
