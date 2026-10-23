(** Executability of the later frame-only secp registrations for every input.
    Reuses the existing fresh-frame constructor and the exact registered
    implementation-to-literal contracts. No intermediate execution, memory
    layout or external-library premise is assumed. These corollaries add no
    jet coverage and do not cover initialized-global or restricted contracts. *)
From Coq Require Import ZArith.
From compcert Require Import Integers.
Require Import C.jet_secp_normalize_local C.jet_frame_constructible_secp.
Require C.jet_secp_negate_literal_contract.
Require C.jet_secp_add_local.
Require C.jet_secp_multiply_literal_jet.
Require C.jet_secp_square_local.
Require C.jet_secp_root_local.
Require C.jet_secp_scalar_zero_local.
Require C.jet_secp_scalar_normalize_local.
Require C.jet_secp_scalar_negate_local.
Require C.jet_secp_scalar_add_local.
Require C.jet_secp_scalar_multiply_local.
Require C.jet_secp_scalar_square_local.
Require C.jet_secp_gej_infinity_local.
Require C.jet_secp_gej_predicate_local.
Require C.jet_secp_gej_negate_local.
Require C.jet_secp_ge_negate_local.
Require C.jet_secp_rescale_local.
Require C.jet_secp_mixed_local.
Require C.jet_secp_gej_add_local.
Require C.jet_secp_gej_ge_equiv_local.
Require C.jet_secp_gej_equiv_local.
Require C.jet_secp_decompress_local.
Require C.jet_secp_curve_local.
Require C.jet_secp_x_equiv_local.
Require C.jet_secp_gej_curve_local.
Require C.jet_secp_double_local.
Set Default Timeout 10.

Local Ltac executable_statement contract :=
 let T := type of contract in
 lazymatch T with secp_jet_local_spec ?f ?A ?B ?spec =>
   exact (secp_jet_runs_on_fresh_frames f A B spec)
 end.
Local Ltac execute_contract contract :=
 apply (secp_jet_local_spec_executable _ _ _ _ contract);
 vm_compute; discriminate.

Theorem fe_negate_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_negate_literal_contract.fe_negate_literal_local_spec).
Proof. execute_contract jet_secp_negate_literal_contract.fe_negate_literal_local_spec. Qed.

Theorem fe_add_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_add_local.fe_add_literal_local_spec).
Proof. execute_contract jet_secp_add_local.fe_add_literal_local_spec. Qed.

Theorem fe_multiply_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec).
Proof. execute_contract jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec. Qed.

Theorem fe_square_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_square_local.fe_square_local_spec).
Proof. execute_contract jet_secp_square_local.fe_square_local_spec. Qed.

Theorem fe_square_root_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_root_local.fe_square_root_literal_local_spec).
Proof. execute_contract jet_secp_root_local.fe_square_root_literal_local_spec. Qed.

Theorem scalar_is_zero_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_zero_local.scalar_zero_local_spec).
Proof. execute_contract jet_secp_scalar_zero_local.scalar_zero_local_spec. Qed.

Theorem scalar_normalize_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_normalize_local.scalar_normalize_local_spec).
Proof. execute_contract jet_secp_scalar_normalize_local.scalar_normalize_local_spec. Qed.

Theorem scalar_negate_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_negate_local.scalar_negate_local_spec).
Proof. execute_contract jet_secp_scalar_negate_local.scalar_negate_local_spec. Qed.

Theorem scalar_add_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_add_local.scalar_add_literal_local_spec).
Proof. execute_contract jet_secp_scalar_add_local.scalar_add_literal_local_spec. Qed.

Theorem scalar_multiply_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_multiply_local.scalar_multiply_literal_local_spec).
Proof. execute_contract jet_secp_scalar_multiply_local.scalar_multiply_literal_local_spec. Qed.

Theorem scalar_square_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_scalar_square_local.scalar_square_literal_local_spec).
Proof. execute_contract jet_secp_scalar_square_local.scalar_square_literal_local_spec. Qed.

Theorem gej_infinity_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_infinity_local.gej_infinity_literal_local_spec).
Proof. execute_contract jet_secp_gej_infinity_local.gej_infinity_literal_local_spec. Qed.

Theorem gej_is_infinity_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_predicate_local.gej_is_infinity_literal_local_spec).
Proof. execute_contract jet_secp_gej_predicate_local.gej_is_infinity_literal_local_spec. Qed.

Theorem gej_negate_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_negate_local.gej_negate_literal_local_spec).
Proof. execute_contract jet_secp_gej_negate_local.gej_negate_literal_local_spec. Qed.

Theorem ge_negate_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_ge_negate_local.ge_negate_literal_local_spec).
Proof. execute_contract jet_secp_ge_negate_local.ge_negate_literal_local_spec. Qed.

Theorem gej_rescale_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_rescale_local.gej_rescale_literal_local_spec).
Proof. execute_contract jet_secp_rescale_local.gej_rescale_literal_local_spec. Qed.

Theorem gej_ge_add_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_mixed_local.gej_ge_add_literal_local_spec).
Proof. execute_contract jet_secp_mixed_local.gej_ge_add_literal_local_spec. Qed.

Theorem gej_add_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_add_local.gej_add_literal_local_spec).
Proof. execute_contract jet_secp_gej_add_local.gej_add_literal_local_spec. Qed.

Theorem gej_ge_equiv_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_ge_equiv_local.gej_ge_equiv_literal_local_spec).
Proof. execute_contract jet_secp_gej_ge_equiv_local.gej_ge_equiv_literal_local_spec. Qed.

Theorem gej_equiv_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_equiv_local.gej_equiv_literal_local_spec).
Proof. execute_contract jet_secp_gej_equiv_local.gej_equiv_literal_local_spec. Qed.

Theorem decompress_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_decompress_local.decompress_literal_local_spec).
Proof. execute_contract jet_secp_decompress_local.decompress_literal_local_spec. Qed.

Theorem ge_is_on_curve_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_curve_local.ge_is_on_curve_literal_local_spec).
Proof. execute_contract jet_secp_curve_local.ge_is_on_curve_literal_local_spec. Qed.

Theorem gej_x_equiv_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_x_equiv_local.gej_x_equiv_literal_local_spec).
Proof. execute_contract jet_secp_x_equiv_local.gej_x_equiv_literal_local_spec. Qed.

Theorem gej_is_on_curve_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_gej_curve_local.gej_is_on_curve_literal_local_spec).
Proof. execute_contract jet_secp_gej_curve_local.gej_is_on_curve_literal_local_spec. Qed.

Theorem gej_double_runs_on_fresh_frames :
 ltac:(executable_statement jet_secp_double_local.gej_double_literal_local_spec).
Proof. execute_contract jet_secp_double_local.gej_double_literal_local_spec. Qed.

