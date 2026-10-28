(** Checked coefficient identity for the original odd-table step 11 to 13.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 240.
Lemma table_step11_coefficients :
 table_witness_step 11%nat=table_witness_scaled_next 11%nat.
Proof. Time vm_compute;reflexivity. Qed.
