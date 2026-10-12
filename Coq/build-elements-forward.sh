#!/usr/bin/env bash
set -euo pipefail

# Elements proofs that need the forward-memory property of Clight executions
# (a helper with an addressable local): Coq/forward/proofs, logical name
# JetForward.  The property is the unaccepted prerequisite
# proof-work/sha-support/jet_clight_forward.v.source of the main checkout; it
# is not copied into this branch but verified against
# startup/PREREQUISITES.sha256 and extracted to startup/prereq (as
# build-startup.sh does).  The Elements modules of Coq/C must already be
# compiled in this tree.
# Usage: SHA_SUPPORT=DIR bash build-elements-forward.sh [--check]
cd "$(dirname "$0")"
: "${SHA_SUPPORT:?Set SHA_SUPPORT to the proof-work/sha-support directory holding the prerequisite}"
mkdir -p startup/prereq
name=jet_clight_forward.v.source
hash=$(awk -v n="$name" '$2 == n {print $1}' startup/PREREQUISITES.sha256)
actual=$(shasum -a 256 "$SHA_SUPPORT/$name" | awk '{print $1}')
[[ -n "$hash" && "$actual" == "$hash" ]] || { echo "prerequisite $name differs from the recorded version" >&2; exit 1; }
cmp -s "$SHA_SUPPORT/$name" "startup/prereq/${name%.source}" || cp "$SHA_SUPPORT/$name" "startup/prereq/${name%.source}"
if grep -nE '\b(admit|Admitted|Axiom|Parameter|Conjecture)\b' forward/proofs/*.v; then
  echo "forbidden declaration in forward sources" >&2; exit 1
fi
paths=(-Q startup/prereq JetStartupReview -Q forward/proofs JetForward)
ulimit -s 65520 2>/dev/null || true
[[ startup/prereq/jet_clight_forward.vo -nt startup/prereq/jet_clight_forward.v ]] ||
  bash build-jets.sh --coqc "${paths[@]}" startup/prereq/jet_clight_forward.v
modules=(jet_elements_issuance_token_then jet_elements_issuance_token_helper jet_elements_issuance_token_jets)
for name in "${modules[@]}"; do
  bash build-jets.sh --coqc "${paths[@]}" "forward/proofs/$name.v"
done
if [[ "${1:-}" == --check ]]; then
  tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-forward-audit.XXXXXX")
  theorems=(elements_issuance_token_amount_local_spec elements_current_issuance_token_amount_local_spec
    elements_issuance_token_amount_local_spec_executable
    elements_current_issuance_token_amount_local_spec_executable
    elements_issuance_token_amount_runs_everywhere elements_current_issuance_token_amount_runs_everywhere)
  {
    echo "Require JetForward.jet_elements_issuance_token_jets."
    for t in "${theorems[@]}"; do
      echo "Goal True. idtac \"@@ $t\". Abort."
      echo "Print Assumptions JetForward.jet_elements_issuance_token_jets.$t."
    done
  } > "$tmp/audit.v"
  bash build-jets.sh --coqc "${paths[@]}" -Q "$tmp" ForwardAudit "$tmp/audit.v" > "$tmp/audit.log" 2>&1
  # same allowed set as the linked startup audit: the six inherited
  # assumptions and the two CompCert properties used by the forward lemma
  python3 linked/audit-linked-startup.py "$tmp/audit.log" $(( ${#theorems[@]} - 1 )) > /dev/null
  echo "assumption audit passed: ${#theorems[@]} theorems within the eight inherited assumptions"
  bash build-jets.sh --coqchk "${paths[@]}" -silent -o JetForward.jet_elements_issuance_token_jets > "$tmp/coqchk.log" 2>&1
  echo "coqchk passed for jet_elements_issuance_token_jets and its dependencies"
  echo "logs: $tmp"
fi
