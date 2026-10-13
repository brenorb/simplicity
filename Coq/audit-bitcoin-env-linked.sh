#!/usr/bin/env bash
set -euo pipefail

# Build the memcpy-linked environment tree, audit the assumptions of the
# linked builder theorems and kernel-check them with their dependencies.
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-bitcoin-env-linked.XXXXXX")
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' bitcoin-env/C/*.v bitcoin-env-linked/C/*.v; then
  echo "forbidden declaration in sources" >&2; exit 1
fi
bash build-bitcoin-env-linked.sh ${JOBS:--j4}
results=(eval_mallocTapEnv_linked eval_mallocTransaction_linked eval_build_txEnv_linked
  mallocTapEnv_raw_cached_hashes_linked mallocTransaction_raw_cached_hashes_linked
  build_environment_linked build_environment_readable_linked)
{
  echo "Require C.jet_bitcoin_env_linked."
  for r in "${results[@]}"; do
    printf 'Goal True. idtac "@@ %s". Abort.\nPrint Assumptions C.jet_bitcoin_env_linked.%s.\n' "$r" "$r"
  done
} > "$tmp/audit.v"
cd "$root/bitcoin-env-linked/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" BitcoinEnvLinkedAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" ${#results[@]}
bash build-jets.sh --coqchk -silent -o C.jet_bitcoin_env_linked > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for C.jet_bitcoin_env_linked and its dependencies"
echo "logs: $tmp"
