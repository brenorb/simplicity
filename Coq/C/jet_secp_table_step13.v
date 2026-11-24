(** Checked coefficient identity for the original odd-table step 13 to 15.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
(* This larger fixed coefficient certificate exceeds six minutes on the
   pinned toolchain. Use the bounded ceiling of the related denominator
   certificates, preserving every coefficient and proof operation. *)
Set Default Timeout 1200.
Lemma table_step13_coefficients :
 table_witness_step 13%nat=table_witness_scaled_next 13%nat.
Proof. Time vm_compute;reflexivity. Qed.
Set Default Timeout 360.
