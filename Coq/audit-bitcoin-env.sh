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
  jet_bitcoin_env_tapenv_link.tap_env_hash_link jet_bitcoin_env_tapenv_link.mallocTapEnv_cached_hashes)
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
bash build-jets.sh --coqchk -silent -o C.jet_bitcoin_env_tapenv_link C.jet_bitcoin_env_hashbuffer > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for C.jet_bitcoin_env_tapenv_link (which requires C.jet_bitcoin_env_tapenv), C.jet_bitcoin_env_hashbuffer and their dependencies"
echo "logs: $tmp"
