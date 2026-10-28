(** Checked coefficient identity for the original odd-table step 5 to 7.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 60.
Lemma table_step5_coefficients :
 table_witness_step 5%nat=table_witness_scaled_next 5%nat.
Proof. Time vm_compute;reflexivity. Qed.
