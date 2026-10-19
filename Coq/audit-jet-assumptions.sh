#!/usr/bin/env bash
# Assumption gate for the public jet theorems.
#
#   audit-jet-assumptions.sh [--update]
#
# Runs `Print Assumptions` for every theorem listed in C/jet_public_theorems.txt,
# per module in that module's own context (jet-records.py), and compares each
# axiom set with C/snapshots/<module>.assumptions. The gate fails when an axiom
# outside the inherited allowlist appears, a theorem's axiom set differs from
# its record (including a newly used inherited axiom), or a listed theorem is
# missing. JET_ONLY_MODULES=FILE restricts the run to the modules in FILE.
# After an intentional change, review the diff and run with --update.
#
# Requires a built project (Coq/build-jets.sh).
set -euo pipefail
cd "$(dirname "$0")"
args=(assumptions)
[[ "${1:-}" == "--update" ]] && args+=(--update)
[[ -n "${JET_ONLY_MODULES:-}" ]] && args+=(--modules "$JET_ONLY_MODULES")
exec python3 jet-records.py "${args[@]}"
