(** Checked coefficient identity for the original odd-table step 13 to 15.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 360.
Lemma table_step13_coefficients :
 table_witness_step 13%nat=table_witness_scaled_next 13%nat.
Proof. Time vm_compute;reflexivity. Qed.
