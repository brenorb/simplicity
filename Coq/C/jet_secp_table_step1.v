(** Checked coefficient identity for the original odd-table step 1 to 3.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 60.
Lemma table_step1_coefficients :
 table_witness_step 1%nat=table_witness_scaled_next 1%nat.
Proof. Time vm_compute;reflexivity. Qed.
