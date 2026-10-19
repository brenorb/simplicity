#!/usr/bin/env bash
# Freeze public theorem types AND the definitions that give their contracts
# meaning. An axiom audit alone cannot detect an impossible added premise or
# a weakened postcondition hidden behind a transparent predicate.
# Changes require review of C/jet_contracts.expected, then an explicit --update.
set -euo pipefail
cd "$(dirname "$0")"
update=false
case "${1:-}" in
  --update) update=true ;;
  "") ;;
  *) echo "usage: $0 [--update]" >&2; exit 2 ;;
esac
work=$(mktemp -d "${TMPDIR:-/tmp}/jet-contracts.XXXXXX")
trap 'rm -rf "$work"' EXIT
{
  echo 'Set Warnings "-notation-overridden".'
  cat C/jet_public_theorems.txt C/jet_contract_definitions.txt |
    awk '!/^#/ && NF==2 {print $1}' | sort -u |
    # Specification-library definitions need loading, not opening. Importing
    # Word here would change the printed names of all existing contracts.
    awk '/^Simplicity\./ {print "Require " $0 "."; next}
         /^C\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}
         /^(C[.]jet_secp_scalar_lambda_global|C[.]jet_clight_forward|C[.]jet_clight_readonly|C[.]jet_clight_readonly_frame|C[.]jet_secp_scalar_lambda_read_state|C[.]jet_secp_scalar_mul512_borrowed|C[.]jet_secp_scalar_mul_borrowed_alloc|C[.]jet_secp_borrowed_product_reduce|C[.]jet_sx_region_lframe|C[.]jet_secp_scalar_mul_borrowed_body|C[.]jet_secp_scalar_mul_borrowed_function|C[.]jet_secp_scalar_mul_borrowed_observed|C[.]jet_secp_scalar_lambda_region|C[.]jet_secp_scalar_lambda_inputs|C[.]jet_secp_canonical_scalar_lambda|C[.]jet_secp_scalar_lambda_from_reader|C[.]jet_secp_scalar_lambda_readonly|C[.]jet_secp_scalar_lambda_call_chain|C[.]jet_secp_scalar_lambda_rest|C[.]jet_secp_scalar_lambda_lifecycle|C[.]jet_secp_scalar_lambda_initialized|C[.]jet_frame_constructible|C[.]jet_secp_scalar_lambda_frame_state|C[.]jet_program_initialization|C[.]jet_secp_scalar_lambda_init_exists|C[.]jet_secp_scalar_lambda_fresh|C[.]jet_secp_initialized_contract|C[.]jet_secp_scalar_lambda_local)$/ {print "Require " $0 "."; next}
         /^C\.jet_forWhile_fold$/ {print "Require " $0 "."; next}
         /^C\.jet_u32_local_init$/ {print "Require " $0 "."; next}
         /^C\.jet_haskell_hash_word$/ {print "Require " $0 "."; next}
         /^C\.jet_application_partial_transport$/ {print "Require " $0 "."; next}
         /^C\.jet_local_alloc_effect$/ {print "Require " $0 "."; next}
         /^(C[.]jet_elements_const_bits|C[.]jet_elements_null_data_cases|C[.]jet_elements_null_data_loads|C[.]jet_elements_null_data_small|C[.]jet_elements_null_data_reserved|C[.]jet_elements_null_data_payload|C[.]jet_elements_bit_expr|C[.]jet_elements_null_data_nonpush|C[.]jet_elements_null_data_opcode|C[.]jet_elements_null_data_index|C[.]jet_elements_null_data_output_guard|C[.]jet_elements_current_reader|C[.]jet_read_after_write|C[.]jet_elements_null_data_read_index|C[.]jet_elements_null_data_guard_compose|C[.]jet_elements_null_data_rest|C[.]jet_elements_null_data_layout|C[.]jet_elements_null_data_bitmachine|C[.]jet_elements_null_data_environment|C[.]jet_application_context_contract|C[.]jet_elements_null_data_contract|C[.]jet_elements_null_data_parse|C[.]jet_application_context_transport|C[.]jet_elements_null_data_literal)$/ {print "Require " $0 "."; next}
         /^C\.jet_elements_/ {print "Require " $0 "."; next}
         {print "Require Import " $0 "."}'
  echo 'Import Simplicity.BitMachine Simplicity.Translate.'
  echo 'Set Printing All.'
  echo 'Set Printing Width 120.'
  awk '!/^#/ && NF==2 {
    explicit = ($1 ~ /^C\.jet_elements_(field_eval|effects|wrapper|transport|call|read_step|steps|index_eval|indexed_exec|indexed_then|env_load|indexed_scalar|indexed_scalar_jets|sequence_literal|current_spec|current_exec|current_jets|current_sequence_literal)$/) || ($1 ~ /^(C[.]jet_elements_write32s_exec|C[.]jet_elements_write32s_layout|C[.]jet_elements_hash_write|C[.]jet_elements_hash_getters|C[.]jet_elements_write8_step|C[.]jet_elements_tapleaf_version_local|C[.]jet_elements_tapleaf_literal|C[.]jet_haskell_hash_word|C[.]jet_elements_script_cmr_local|C[.]jet_elements_genesis_hash_local|C[.]jet_elements_hash_literal)$/) || ($1 ~ /^(C[.]jet_elements_tx_field_set|C[.]jet_elements_is_final_spec|C[.]jet_elements_is_final_local|C[.]jet_elements_lock_spec|C[.]jet_elements_lock_exec|C[.]jet_elements_lock_local|C[.]jet_elements_lock_literal|C[.]jet_elements_prim_sem|C[.]jet_elements_bool_wrapper|C[.]jet_elements_check_lock|C[.]jet_application_partial_transport|C[.]jet_elements_check_lock_literal|C[.]jet_elements_indexed_ptr_then|C[.]jet_elements_indexed_ptr|C[.]jet_elements_hash_helpers|C[.]jet_elements_indexed_ptr_jets|C[.]jet_elements_hash_elem|C[.]jet_elements_pegin_local|C[.]jet_elements_input_hash_jets|C[.]jet_elements_asset_helper|C[.]jet_elements_asset_jets|C[.]jet_elements_amt_helper|C[.]jet_elements_indexed_gen|C[.]jet_elements_indexed_ptr2|C[.]jet_elements_amount_jets|C[.]jet_elements_issuance_helper|C[.]jet_elements_issuance_jets|C[.]jet_elements_issuance_amount_jets|C[.]jet_elements_current_ptr|C[.]jet_elements_current_ptr_jets|C[.]jet_elements_current_gen|C[.]jet_elements_current_input_jets|C[.]jet_elements_current_gen_jets|C[.]jet_elements_pegin_literal)$/) || ($1 ~ /^(C[.]jet_elements_script_hash_literal|C[.]jet_elements_issuance_proof_literal)$/) || ($1 ~ /^(C[.]jet_elements_annex_local|C[.]jet_elements_optional_digest_literal|C[.]jet_elements_issuance_digest_literal|C[.]jet_elements_indexed_literal|C[.]jet_elements_output_proof_jets|C[.]jet_elements_output_proof_literal)$/) || ($1 ~ /^(C[.]jet_elements_hash_getter_local|C[.]jet_elements_hash_getter_writehash|C[.]jet_elements_hash_field_jets|C[.]jet_elements_tappath_local|C[.]jet_elements_tappath_nullable|C[.]jet_elements_tap_getters_literal)$/) || ($1 ~ /^(C[.]jet_u32_local_init|C[.]jet_elements_lbtc_asset_exec|C[.]jet_elements_lbtc_asset_local)$/) || ($1 ~ /^(C[.]jet_forWhile_fold|C[.]jet_elements_legacy_lock_spec|C[.]jet_elements_legacy_lock_exec|C[.]jet_elements_legacy_lock_local)$/) || ($1 ~ /^(C[.]jet_elements_legacy_check)$/) || ($1 ~ /^(C[.]jet_elements_output_nonce_literal)$/) || ($1 ~ /^(C[.]jet_elements_asset_literal)$/) || ($1 ~ /^(C[.]jet_elements_amount_literal)$/) || ($1 ~ /^(C[.]jet_elements_issuance_amount_literal)$/) || ($1 ~ /^(C[.]jet_elements_token_zero_init|C[.]jet_elements_token_select|C[.]jet_local_alloc_effect|C[.]jet_elements_token_amount_exec|C[.]jet_elements_token_amount_jets|C[.]jet_elements_token_amount_literal)$/) || ($1 ~ /^(C[.]jet_elements_transaction_id_literal)$/) || ($1 ~ /^(C[.]jet_elements_const_bits|C[.]jet_elements_null_data_cases|C[.]jet_elements_null_data_loads|C[.]jet_elements_null_data_small|C[.]jet_elements_null_data_reserved|C[.]jet_elements_null_data_payload|C[.]jet_elements_bit_expr|C[.]jet_elements_null_data_nonpush|C[.]jet_elements_null_data_opcode|C[.]jet_elements_null_data_index|C[.]jet_elements_null_data_output_guard|C[.]jet_elements_current_reader|C[.]jet_read_after_write|C[.]jet_elements_null_data_read_index|C[.]jet_elements_null_data_guard_compose|C[.]jet_elements_null_data_rest|C[.]jet_elements_null_data_layout|C[.]jet_elements_null_data_bitmachine|C[.]jet_elements_null_data_environment|C[.]jet_application_context_contract|C[.]jet_elements_null_data_contract|C[.]jet_elements_null_data_parse|C[.]jet_application_context_transport|C[.]jet_elements_null_data_literal)$/) || ($1 ~ /^(C[.]jet_secp_scalar_lambda_global|C[.]jet_clight_forward|C[.]jet_clight_readonly|C[.]jet_clight_readonly_frame|C[.]jet_secp_scalar_lambda_read_state|C[.]jet_secp_scalar_mul512_borrowed|C[.]jet_secp_scalar_mul_borrowed_alloc|C[.]jet_secp_borrowed_product_reduce|C[.]jet_sx_region_lframe|C[.]jet_secp_scalar_mul_borrowed_body|C[.]jet_secp_scalar_mul_borrowed_function|C[.]jet_secp_scalar_mul_borrowed_observed|C[.]jet_secp_scalar_lambda_region|C[.]jet_secp_scalar_lambda_inputs|C[.]jet_secp_canonical_scalar_lambda|C[.]jet_secp_scalar_lambda_from_reader|C[.]jet_secp_scalar_lambda_readonly|C[.]jet_secp_scalar_lambda_call_chain|C[.]jet_secp_scalar_lambda_rest|C[.]jet_secp_scalar_lambda_lifecycle|C[.]jet_secp_scalar_lambda_initialized|C[.]jet_frame_constructible|C[.]jet_secp_scalar_lambda_frame_state|C[.]jet_program_initialization|C[.]jet_secp_scalar_lambda_init_exists|C[.]jet_secp_scalar_lambda_fresh|C[.]jet_secp_initialized_contract|C[.]jet_secp_scalar_lambda_local)$/)
    printf "Check %s%s.%s.\n", (explicit ? "@" : ""), $1, $2
  }' C/jet_public_theorems.txt
  awk '!/^#/ && NF==2 {printf "Print %s.%s.\n", $1, $2}' C/jet_contract_definitions.txt
} > "$work/contracts.v"
# Coq sometimes leaves blanks at line ends; they are not part of the contract.
bash build-jets.sh --coqc -q "$work/contracts.v" |
  sed 's/[[:blank:]]*$//' > "$work/contracts.out"
if $update; then
  cp "$work/contracts.out" C/jet_contracts.expected
  echo 'updated C/jet_contracts.expected; review the contract diff'
elif ! diff -u C/jet_contracts.expected "$work/contracts.out"; then
  echo 'public theorem contracts changed' >&2
  exit 1
else
  echo 'public theorem contracts match C/jet_contracts.expected'
fi
