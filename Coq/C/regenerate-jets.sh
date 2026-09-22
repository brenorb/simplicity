#!/usr/bin/env bash
set -euo pipefail

# Genuine glibc target headers are required; host macOS headers are not a
# substitute. See JET_PROOFS.md for a pinned Debian header package and checksum.
: "${COMPCERT:?Set COMPCERT to the built CompCert 3.14 source directory}"
: "${JET_SYSROOT:?Set JET_SYSROOT to an extracted amd64 libc6-dev sysroot}"
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
cd "$jet_repo"
jet_work=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-clightgen.XXXXXX")
# Keep the generated configuration for auditing; no source headers are changed.
sed -e "s|@COMPCERT@|$COMPCERT|g" -e "s|@SYSROOT@|$JET_SYSROOT|g" \
  Coq/C/clightgen-linux.ini.in > "$jet_work/clightgen.ini"
"$COMPCERT/clightgen" -conf "$jet_work/clightgen.ini" \
  -U__clang__ -U__clang_major__ -U__clang_minor__ \
  -std=c11 -normalize -fstruct-passing -DNDEBUG -DRECKLESS \
  -IC -IC/include -o "${1:-Coq/C/jets.v}" Coq/C/jet_translation_unit.c
printf 'clightgen configuration retained at %s\n' "$jet_work/clightgen.ini"
