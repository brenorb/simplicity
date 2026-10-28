(** Checked coefficient identity for the original odd-table step 7 to 9.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
Set Default Timeout 60.
Lemma table_step7_coefficients :
 table_witness_step 7%nat=table_witness_scaled_next 7%nat.
Proof. Time vm_compute;reflexivity. Qed.
