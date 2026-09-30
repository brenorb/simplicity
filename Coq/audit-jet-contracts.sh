#!/usr/bin/env bash
# Freeze public theorem types AND the definitions that give their contracts
# meaning. An axiom audit alone cannot detect an impossible added premise or
# a weakened postcondition hidden behind a transparent predicate.
# Changes require review of C/jet_contracts.expected, then an explicit --update.
set -euo pipefail
cd "$(dirname "$0")"
update=false
case "${1:-}" in
  --update) update=true ;;
  "") ;;
  *) echo "usage: $0 [--update]" >&2; exit 2 ;;
esac
work=$(mktemp -d "${TMPDIR:-/tmp}/jet-contracts.XXXXXX")
trap 'rm -rf "$work"' EXIT
{
  echo 'Set Warnings "-notation-overridden".'
  cat C/jet_public_theorems.txt C/jet_contract_definitions.txt |
    awk '!/^#/ && NF==2 {print $1}' | sort -u |
    sed 's/^/Require Import /; s/$/./'
  echo 'Set Printing All.'
  echo 'Set Printing Width 120.'
  awk '!/^#/ && NF==2 {printf "Check %s.%s.\n", $1, $2}' C/jet_public_theorems.txt
  awk '!/^#/ && NF==2 {printf "Print %s.%s.\n", $1, $2}' C/jet_contract_definitions.txt
} > "$work/contracts.v"
# Coq sometimes leaves blanks at line ends; they are not part of the contract.
bash build-jets.sh --coqc -q "$work/contracts.v" |
  sed 's/[[:blank:]]*$//' > "$work/contracts.out"
if $update; then
  cp "$work/contracts.out" C/jet_contracts.expected
  echo 'updated C/jet_contracts.expected; review the contract diff'
elif ! diff -u C/jet_contracts.expected "$work/contracts.out"; then
  echo 'public theorem contracts changed' >&2
  exit 1
else
  echo 'public theorem contracts match C/jet_contracts.expected'
fi
