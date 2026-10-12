#!/usr/bin/env bash
set -euo pipefail

# Build the Elements environment-unit derived tree, check that the generated
# ports are current, reject admissions, audit the assumptions of the result
# theorem and kernel-check it with its whole dependency chain.
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-env.XXXXXX")
mkdir "$tmp/C"
python3 elements-env/gen-elements-env-ports.py "$tmp/C" > /dev/null
for f in "$tmp"/C/*.v; do
  cmp "$f" "elements-env/C/$(basename "$f")" || { echo "stale generated module $(basename "$f")" >&2; exit 1; }
done
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' elements-env/C/*.v; then
  echo "forbidden declaration in elements-env sources" >&2; exit 1
fi
bash build-elements-env.sh ${JOBS:--j4}
{
  echo "Require C.jet_elements_env_tapenv C.jet_elements_env_tomidstate C.jet_elements_env_ctxo."
  for r in jet_elements_env_tomidstate.eval_sha256_toMidstate jet_elements_env_ctxo.ctxo_hash jet_elements_env_tapenv.eval_mallocTapEnv; do
    printf 'Goal True. idtac "@@ %s". Abort.\nPrint Assumptions C.%s.\n' "${r#*.}" "$r"
  done
} > "$tmp/audit.v"
cd "$root/elements-env/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" ElementsEnvAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" 3
bash build-jets.sh --coqchk -silent -o C.jet_elements_env_tapenv > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for C.jet_elements_env_tapenv and its dependencies"
echo "logs: $tmp"
