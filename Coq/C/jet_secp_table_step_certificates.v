(** Dispatch the seven closed coefficient checks used by the literal table. *)
From Coq Require Import List.
Require Import C.jet_secp_table_coordinates C.jet_secp_table_step_nonzero
 C.jet_secp_table_step1 C.jet_secp_table_step3 C.jet_secp_table_step5
 C.jet_secp_table_step7 C.jet_secp_table_step9 C.jet_secp_table_step11 C.jet_secp_table_step13.
Set Default Timeout 10.
Theorem table_witness_step_checked n : In n table_step_indices ->
 table_witness_step n=table_witness_scaled_next n.
Proof.
 unfold table_step_indices;intro Member.
 destruct Member as [Equal|Member].
 { subst n;exact table_step1_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step3_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step5_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step7_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step9_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step11_coefficients. }
 destruct Member as [Equal|Member].
 { subst n;exact table_step13_coefficients. }
 contradiction.
Qed.
