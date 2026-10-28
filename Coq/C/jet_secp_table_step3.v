(** Checked coefficient identity for the original odd-table step 3 to 5.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 60.
Lemma table_step3_coefficients :
 table_witness_step 3%nat=table_witness_scaled_next 3%nat.
Proof. Time vm_compute;reflexivity. Qed.
