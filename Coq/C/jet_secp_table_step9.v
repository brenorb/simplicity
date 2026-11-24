(** Checked coefficient identity for the original odd-table step 9 to 11.
    Its use for literal word operations requires the separate residue bridge. *)
Require Import C.jet_secp_table_coordinates.
(* This coefficient certificate exceeds the former 60-second ceiling on
   the pinned toolchain. Match the bounded budget of the adjacent step. *)
Set Default Timeout 240.
Lemma table_step9_coefficients :
 table_witness_step 9%nat=table_witness_scaled_next 9%nat.
Proof. Time vm_compute;reflexivity. Qed.
Set Default Timeout 60.
