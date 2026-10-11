#!/usr/bin/env bash
set -euo pipefail

# Verify the memcpy-linked proofs: (re)build the derived tree, check that the
# generated theorem modules are up to date, audit the assumptions of every
# linked theorem, and re-check all linked modules and their whole dependency
# chains with the independent kernel checker (coqchk).
cd "$(dirname "$0")"
root=$PWD
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-linked-audit.XXXXXX")
mkdir "$tmp/C"
python3 linked/gen-linked-theorems.py C "$tmp/C/jet_linked_memcpy_jets.v"
python3 linked/gen-linked-sha-theorems.py C "$tmp/C"
for f in "$tmp"/C/*.v; do
  cmp "$f" "linked/C/$(basename "$f")" || { echo "stale generated module $(basename "$f")" >&2; exit 1; }
done
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' linked/C/*.v C/jet_memcpy_exact.v C/jet_memcpy_impl.v; then
  echo "forbidden declaration in linked sources" >&2; exit 1
fi
bash build-linked.sh "${JOBS:--j4}"
python3 linked/audit-linked.py gen linked/C "$tmp/audit.v"
cd linked/tree
ulimit -s 65520 2>/dev/null || true
bash build-jets.sh --coqc -Q "$tmp" LinkedAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
python3 "$root/linked/audit-linked.py" check "$root/linked/C" "$tmp/audit.log"
modules=()
for f in "$root"/linked/C/*.v; do name=$(basename "$f"); modules+=("C.${name%.v}"); done
bash build-jets.sh --coqchk -silent -o "${modules[@]}" > "$tmp/coqchk.log" 2>&1
echo "coqchk passed for ${#modules[@]} linked modules and their dependencies"
echo "logs: $tmp"
