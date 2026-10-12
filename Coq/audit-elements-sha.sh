#!/usr/bin/env bash
set -euo pipefail

# Build the Elements-SHA derived tree, check that every generated module is
# current, audit the assumptions of its theorems and kernel-check them with
# their whole dependency chains.  The start-up invariant modules are included
# when the archived prerequisites are present (see build-elements-sha.sh).
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-sha.XXXXXX")
mkdir "$tmp/C" "$tmp/startup"
python3 elements-sha/gen-elements-sha-theorems.py C "$tmp/C/jet_elements_sha_jets.v" > /dev/null
python3 elements-sha/gen-elements-sha-ports.py "$tmp/C" > /dev/null
python3 elements-sha/gen-elements-tap-ports.py "$tmp/C" > /dev/null
python3 elements-sha/gen-elements-startup.py "$tmp/startup" > /dev/null
for f in "$tmp"/C/*.v; do
  cmp "$f" "elements-sha/C/$(basename "$f")" || { echo "stale generated module $(basename "$f")" >&2; exit 1; }
done
for f in "$tmp"/startup/*.v; do
  cmp "$f" "elements-sha/startup/$(basename "$f")" || { echo "stale generated module $(basename "$f")" >&2; exit 1; }
done
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' elements-sha/C/*.v elements-sha/startup/*.v; then
  echo "forbidden declaration in elements-sha sources" >&2; exit 1
fi
bash build-elements-sha.sh ${JOBS:--j4}
startup=0
[[ -e elements-sha/tree/startup/elements/jet_elements_startup_jets.vo ]] && startup=1
paths=()
modules=(C.jet_elements_sha_jets C.jet_elements_hash_jets)
report() { printf 'Goal True. idtac "@@ %s". Abort.\nPrint Assumptions %s.\n' "$1" "$2"; }
{
  echo "Require C.jet_elements_sha_jets C.jet_elements_sha_program C.jet_elements_hash_jets."
  report elements_sha_genv C.jet_elements_sha_program.elements_sha_genv
  for mod in jet_elements_sha_jets jet_elements_hash_jets; do
    for name in $(grep -oE '^Theorem [a-z0-9_]*_local_spec_elements' "elements-sha/C/$mod.v" | awk '{print $2}'); do
      report "$name" "C.$mod.$name"
    done
  done
  if [[ $startup == 1 ]]; then
    echo "Require ElementsStartup.jet_elements_startup_state ElementsStartup.jet_elements_startup_jets."
    report "elements_startup_state_initialized forward" ElementsStartup.jet_elements_startup_state.elements_startup_state_initialized
    for name in $(grep -oE '^Theorem [a-z0-9_]*_startup_spec' elements-sha/startup/jet_elements_startup_jets.v | awk '{print $2}'); do
      report "$name forward" "ElementsStartup.jet_elements_startup_jets.$name"
    done
  fi
} > "$tmp/audit.v"
expected=18
if [[ $startup == 1 ]]; then
  expected=36
  paths=(-Q startup/prereq JetStartupReview -Q startup/proofs JetStartup -Q startup/elements ElementsStartup)
  modules+=(ElementsStartup.jet_elements_startup_state ElementsStartup.jet_elements_startup_jets)
fi
cd "$root/elements-sha/tree"
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc "${paths[@]}" -Q "$tmp" ElementsShaAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/elements-sha/audit.py" "$tmp/audit.log" $expected
bash build-jets.sh --coqchk "${paths[@]}" -silent -o "${modules[@]}" > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for ${modules[*]} and their dependencies"
echo "logs: $tmp"
