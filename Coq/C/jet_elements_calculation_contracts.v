(** Public names for the recovered original-C calculation contracts.
    The libc model and concrete initial SHA global values remain explicit. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_output_layout.
Require Import C.jet_write_layout C.jet_encoding C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local.
Require Import C.jet_elements_issuance_calc_spec C.jet_calculation_calls_calculation_calls.
Require Import C.jet_calculation_local_local.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem calculate_asset_canonical_local_spec : memcpy_model ->
  calculation_jet_local_spec f_simplicity_calculate_asset
    (@calculate_asset_spec Alg.CoreFunSem).
Proof. exact calculate_asset_local_spec. Qed.

Theorem calculate_explicit_token_canonical_local_spec : memcpy_model ->
  calculation_jet_local_spec f_simplicity_calculate_explicit_token
    (@calculate_explicit_token_spec Alg.CoreFunSem).
Proof. exact calculate_explicit_token_local_spec. Qed.

Theorem calculate_confidential_token_canonical_local_spec : memcpy_model ->
  calculation_jet_local_spec f_simplicity_calculate_confidential_token
    (@calculate_confidential_token_spec Alg.CoreFunSem).
Proof. exact calculate_confidential_token_local_spec. Qed.
