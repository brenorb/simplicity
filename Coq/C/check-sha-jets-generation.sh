#!/usr/bin/env bash
set -euo pipefail

# Regenerate only into a fresh directory; never overwrite the checked artifact.
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
jet_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-sha-jets-check.XXXXXX")
bash "$jet_repo/Coq/C/regenerate-sha-jets.sh" "$jet_check_dir/jets_sha.v"
cmp "$jet_repo/Coq/C/jets_sha.v" "$jet_check_dir/jets_sha.v"
printf 'Generated SHA AST matches; checked copy: %s\n' "$jet_check_dir/jets_sha.v"
