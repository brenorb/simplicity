#!/usr/bin/env bash
# Freeze public theorem types AND the definitions that give their contracts
# meaning. An axiom audit alone cannot detect an impossible added premise or
# a weakened postcondition hidden behind a transparent predicate.
#
#   audit-jet-contracts.sh [--update]
#
# Records are per module (C/snapshots/<module>.contracts), each printed in its
# own module's context by jet-records.py. JET_ONLY_MODULES=FILE restricts the
# run to the modules listed in FILE. Changes require review of the snapshot
# diff, then an explicit --update.
set -euo pipefail
cd "$(dirname "$0")"
args=(contracts)
case "${1:-}" in
  --update) args+=(--update) ;;
  "") ;;
  *) echo "usage: $0 [--update]" >&2; exit 2 ;;
esac
[[ -n "${JET_ONLY_MODULES:-}" ]] && args+=(--modules "$JET_ONLY_MODULES")
exec python3 jet-records.py "${args[@]}"
