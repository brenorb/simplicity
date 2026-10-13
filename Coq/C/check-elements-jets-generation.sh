#!/usr/bin/env bash
set -euo pipefail

# Regenerate into a fresh directory, never over the checked artifact.
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
jet_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-jets-check.XXXXXX")
bash "$jet_repo/Coq/C/regenerate-elements-jets.sh" "$jet_check_dir/jets_elements.v"
cmp "$jet_repo/Coq/C/jets_elements.v" "$jet_check_dir/jets_elements.v"
printf 'Generated Elements AST matches; checked copy: %s\n' "$jet_check_dir/jets_elements.v"
