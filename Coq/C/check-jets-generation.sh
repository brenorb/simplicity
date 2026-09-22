#!/usr/bin/env bash
set -euo pipefail

# Read-only with respect to the committed artifact. Retain generated files for
# inspection on either success or failure; all writes stay in a fresh directory.
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
jet_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-jets-check.XXXXXX")
bash "$jet_repo/Coq/C/regenerate-jets.sh" "$jet_check_dir/jets.v"
cmp "$jet_repo/Coq/C/jets.v" "$jet_check_dir/jets.v"
printf 'Generated AST matches the committed artifact; checked copy: %s\n' "$jet_check_dir/jets.v"
