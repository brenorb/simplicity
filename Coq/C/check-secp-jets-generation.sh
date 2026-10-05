#!/usr/bin/env bash
set -euo pipefail

# Regenerate only into a fresh directory; never overwrite the checked artifact.
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
jet_check_dir=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-secp-jets-check.XXXXXX")
bash "$jet_repo/Coq/C/regenerate-secp-jets.sh" "$jet_check_dir/jets_secp.v"
cmp "$jet_repo/Coq/C/jets_secp.v" "$jet_check_dir/jets_secp.v"
printf 'Generated secp256k1 AST matches; checked copy: %s\n' "$jet_check_dir/jets_secp.v"
