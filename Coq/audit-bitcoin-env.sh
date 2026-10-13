#!/usr/bin/env bash
set -euo pipefail

# Build the environment-unit derived tree, check that the generated module
# is current, reject admissions, audit the assumptions of the result
# theorems and kernel-check them with their whole dependency chains.
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-bitcoin-env.XXXXXX")
python3 bitcoin-env/gen-env-field-eval.py "$tmp/jet_bitcoin_env_field_eval.v"
cmp "$tmp/jet_bitcoin_env_field_eval.v" bitcoin-env/C/jet_bitcoin_env_field_eval.v || {
  echo "stale generated module jet_bitcoin_env_field_eval.v" >&2; exit 1; }
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' bitcoin-env/C/*.v; then
  echo "forbidden declaration in bitcoin-env sources" >&2; exit 1
fi
bash build-bitcoin-env.sh ${JOBS:--j4}
results=(jet_bitcoin_env_tomidstate.eval_sha256_toMidstate jet_bitcoin_env_hashbuffer.eval_hashBuffer
  jet_bitcoin_env_malloc.eval_malloc jet_bitcoin_env_ctxo.ctxo_init jet_bitcoin_env_ctxo.ctxo_hash
  jet_bitcoin_env_ctxo.ctxo_finalize jet_bitcoin_env_tapenv.eval_mallocTapEnv
  jet_bitcoin_env_tapenv_link.tapleaf_hash_link jet_bitcoin_env_tapenv_link.tappath_hash_link
  jet_bitcoin_env_tapenv_link.tap_env_hash_link jet_bitcoin_env_tapenv_link.mallocTapEnv_cached_hashes
  jet_bitcoin_env_tapenv_describe.tapenv_describes_exists
  jet_bitcoin_env_copyoutput.eval_copyOutput jet_bitcoin_env_copyinput.eval_copyInput
  jet_bitcoin_env_tx_inexec.mt_inblock_exec jet_bitcoin_env_tx_outblock.mt_outblock_exec
  jet_bitcoin_env_tx_txhash.mt_txhash jet_bitcoin_env_tx.eval_mallocTransaction
  jet_bitcoin_env_tx_link.tx_cached_hashes jet_bitcoin_env_tx_link.mallocTransaction_cached_hashes
  jet_bitcoin_env_bytestring.hash_buffer_bytestring jet_bitcoin_env_tx_raw.raw_tx_describes
  jet_bitcoin_env_tx_raw.mallocTransaction_raw_cached_hashes
  jet_bitcoin_env_tapenv_raw.raw_tapenv_describes
  jet_bitcoin_env_tapenv_raw.mallocTapEnv_raw_cached_hashes
  jet_bitcoin_env_free.eval_freeTransaction jet_bitcoin_env_free.eval_freeTapEnv
  jet_bitcoin_env_txenv.eval_build_txEnv jet_bitcoin_env_txenv_link.sigall_link
  jet_bitcoin_env_build.build_environment jet_bitcoin_env_lifecycle.free_environment
  jet_bitcoin_env_relations.ready_version jet_bitcoin_env_relations.ready_lock_time
  jet_bitcoin_env_relations.ready_num_inputs jet_bitcoin_env_relations.ready_num_outputs
  jet_bitcoin_env_relations.ready_total_input_value
  jet_bitcoin_env_relations.ready_total_output_value jet_bitcoin_env_relations.ready_fee
  jet_bitcoin_env_relations.ready_tx_is_final jet_bitcoin_env_relations.ready_lock
  jet_bitcoin_env_relations.ready_check_lock jet_bitcoin_env_relations.ready_current_index
  jet_bitcoin_env_relations.ready_output_values_hash
  jet_bitcoin_env_relations.ready_output_scripts_hash jet_bitcoin_env_relations.ready_outputs_hash
  jet_bitcoin_env_relations.ready_input_outpoints_hash
  jet_bitcoin_env_relations.ready_input_values_hash
  jet_bitcoin_env_relations.ready_input_scripts_hash
  jet_bitcoin_env_relations.ready_input_utxos_hash
  jet_bitcoin_env_relations.ready_input_sequences_hash
  jet_bitcoin_env_relations.ready_input_annexes_hash
  jet_bitcoin_env_relations.ready_input_script_sigs_hash jet_bitcoin_env_relations.ready_inputs_hash
  jet_bitcoin_env_relations.ready_tx_hash jet_bitcoin_env_relations.ready_tapleaf_hash
  jet_bitcoin_env_relations.ready_tappath_hash jet_bitcoin_env_relations.ready_tap_env_hash
  jet_bitcoin_env_relations.ready_internal_key jet_bitcoin_env_relations.ready_sig_all_hash
  jet_bitcoin_env_relations.ready_transaction_id jet_bitcoin_env_relations.ready_script_cmr
  jet_bitcoin_env_relations.ready_tapleaf_version jet_bitcoin_env_relations.ready_tappath
  jet_bitcoin_env_relations_indexed.ready_input_sequence
  jet_bitcoin_env_relations_indexed.ready_input_value
  jet_bitcoin_env_relations_indexed.ready_input_prev_outpoint
  jet_bitcoin_env_relations_indexed.ready_input_script_hash
  jet_bitcoin_env_relations_indexed.ready_input_script_sig_hash
  jet_bitcoin_env_relations_indexed.ready_input_annex_hash
  jet_bitcoin_env_relations_indexed.ready_current_value
  jet_bitcoin_env_relations_indexed.ready_current_sequence
  jet_bitcoin_env_relations_indexed.ready_current_prev_outpoint
  jet_bitcoin_env_relations_indexed.ready_current_script_hash
  jet_bitcoin_env_relations_indexed.ready_current_script_sig_hash
  jet_bitcoin_env_relations_indexed.ready_current_annex_hash
  jet_bitcoin_env_relations_indexed.ready_distance
  jet_bitcoin_env_relations_indexed.ready_output_value
  jet_bitcoin_env_relations_indexed.ready_output_script_hash
  jet_bitcoin_env_relations_indexed.ready_input_hash
  jet_bitcoin_env_relations_indexed.ready_input_utxo_hash
  jet_bitcoin_env_relations_indexed.ready_output_hash)
{
  for r in "${results[@]}"; do echo "Require C.${r%%.*}."; done
  for r in "${results[@]}"; do
    printf 'Goal True. idtac "@@ %s". Abort.\nPrint Assumptions C.%s.\n' "${r#*.}" "$r"
  done
} > "$tmp/audit.v"
cd "$root/bitcoin-env/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" BitcoinEnvAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" ${#results[@]}
bash build-jets.sh --coqchk -silent -o C.jet_bitcoin_env_tapenv_link C.jet_bitcoin_env_tapenv_describe C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_relations_indexed C.jet_bitcoin_env_lifecycle > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for C.jet_bitcoin_env_tapenv_link (which requires C.jet_bitcoin_env_tapenv), C.jet_bitcoin_env_tapenv_describe, C.jet_bitcoin_env_hashbuffer, C.jet_bitcoin_env_relations_indexed (which requires the three builders, their links to the raw environment, build_environment and both relation sweeps), C.jet_bitcoin_env_lifecycle and their dependencies"
echo "logs: $tmp"
