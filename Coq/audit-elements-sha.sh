#!/usr/bin/env bash
set -euo pipefail

# Build the Elements-SHA derived tree, check that the generated restatement
# module is current, audit the assumptions of its theorems and kernel-check
# it with its whole dependency chain.
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-sha.XXXXXX")
python3 elements-sha/gen-elements-sha-theorems.py C "$tmp/jet_elements_sha_jets.v" > /dev/null
cmp "$tmp/jet_elements_sha_jets.v" elements-sha/C/jet_elements_sha_jets.v || {
  echo "stale generated module jet_elements_sha_jets.v" >&2; exit 1; }
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' elements-sha/C/*.v; then
  echo "forbidden declaration in elements-sha sources" >&2; exit 1
fi
bash build-elements-sha.sh ${JOBS:--j4}
{
  echo "Require C.jet_elements_sha_jets C.jet_elements_sha_program."
  echo 'Goal True. idtac "@@ elements_sha_genv". Abort.'
  echo "Print Assumptions C.jet_elements_sha_program.elements_sha_genv."
  grep -oE '^Theorem [a-z0-9_]*_local_spec_elements' elements-sha/C/jet_elements_sha_jets.v |
    awk '{print "Goal True. idtac \"@@ " $2 "\". Abort.\nPrint Assumptions C.jet_elements_sha_jets." $2 "."}'
} > "$tmp/audit.v"
cd "$root/elements-sha/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" ElementsShaAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" 15
bash build-jets.sh --coqchk -silent -o C.jet_elements_sha_jets > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for jet_elements_sha_jets and its dependencies"
echo "logs: $tmp"
