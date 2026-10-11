#!/usr/bin/env bash
set -euo pipefail

# Compile the startup-invariant modules against the memcpy-linked SHA program
# and derive the contracts that need neither the libc premise nor any premise
# about C global objects.  Run build-linked.sh first; SHA_SUPPORT is as for
# build-startup.sh.  With --check, also audit assumptions and run coqchk.
cd "$(dirname "$0")"
root=$PWD
: "${SHA_SUPPORT:?Set SHA_SUPPORT to the proof-work/sha-support directory holding the prerequisites}"
tree=$root/linked/tree
[[ -f "$tree/C/jets_sha.vo" ]] || { echo "run build-linked.sh first" >&2; exit 1; }
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-linked-startup.XXXXXX")
python3 linked/gen-linked-startup-theorems.py startup/proofs "$tmp/jet_sha_startup_linked.v"
cmp "$tmp/jet_sha_startup_linked.v" linked/startup/jet_sha_startup_linked.v || {
  echo "stale generated module jet_sha_startup_linked.v" >&2; exit 1; }
mkdir -p "$tree/startup/prereq" "$tree/startup/proofs"
order=(jet_clight_forward jet_sha_initial_globals)
while read -r hash name; do
  actual=$(shasum -a 256 "$SHA_SUPPORT/$name" | awk '{print $1}')
  [[ "$actual" == "$hash" ]] || { echo "prerequisite $name differs from the recorded version" >&2; exit 1; }
  dest="$tree/startup/prereq/${name%.source}"
  cmp -s "$SHA_SUPPORT/$name" "$dest" || { rm -f "$dest"; cp "$SHA_SUPPORT/$name" "$dest"; }
done < startup/PREREQUISITES.sha256
modules=(jet_sha_startup_globals jet_sha_startup_state jet_sha_startup_jets jet_sha_startup_env_jets jet_sha_startup_setup jet_sha_startup_env_callers
  jet_sha_startup_executable jet_sha_startup_runs jet_sha_startup_lifecycle)
for name in "${modules[@]}"; do ln -sf "$root/startup/proofs/$name.v" "$tree/startup/proofs/$name.v"; done
ln -sf "$root/linked/startup/jet_sha_startup_linked.v" "$tree/startup/proofs/jet_sha_startup_linked.v"
modules+=(jet_sha_startup_linked)
cd "$tree"
paths=(-Q startup/prereq JetStartupReview -Q startup/proofs JetStartup)
ulimit -s 65520 2>/dev/null || true
# shared frame-construction module (accepted-tree source, compiled here against the linked tree)
for name in jet_word_repr jet_frame_constructible; do
  [[ "C/$name.vo" -nt "C/$name.v" ]] || bash build-jets.sh --coqc "C/$name.v"
done
for name in "${order[@]}"; do bash build-jets.sh --coqc "${paths[@]}" "startup/prereq/$name.v"; done
for name in "${modules[@]}"; do bash build-jets.sh --coqc "${paths[@]}" "startup/proofs/$name.v"; done
if [[ "${1:-}" == --check ]]; then
  {
    echo "Require JetStartup.jet_sha_startup_linked JetStartup.jet_sha_startup_state."
    echo 'Goal True. idtac "@@ sha_startup_state_initialized". Abort.'
    echo "Print Assumptions JetStartup.jet_sha_startup_state.sha_startup_state_initialized."
    grep -oE '^Theorem [a-z0-9_]*_startup(_env|_runs)?_linked' "$root/linked/startup/jet_sha_startup_linked.v" |
      awk '{print "Goal True. idtac \"@@ " $2 "\". Abort.\nPrint Assumptions JetStartup.jet_sha_startup_linked." $2 "."}'
  } > "$tmp/audit.v"
  bash build-jets.sh --coqc "${paths[@]}" -Q "$tmp" LinkedStartupAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
  python3 "$root/linked/audit-linked-startup.py" "$tmp/audit.log" 40
  bash build-jets.sh --coqchk "${paths[@]}" -silent -o JetStartup.jet_sha_startup_linked > "$tmp/coqchk.log" 2>&1
  echo "coqchk passed for jet_sha_startup_linked and its dependencies"
  echo "logs: $tmp"
fi
