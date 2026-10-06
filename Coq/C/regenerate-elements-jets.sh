#!/usr/bin/env bash
set -euo pipefail

# Preparatory generation tool; Elements has no accepted proof chain yet.
# Same pinned target and PRODUCTION configuration as the core jet artifact.
: "${COMPCERT:?Set COMPCERT to the built CompCert 3.14 source directory}"
: "${JET_SYSROOT:?Set JET_SYSROOT to an extracted amd64 libc6-dev sysroot}"
jet_repo=$(cd "$(dirname "$0")/../.." && pwd)
cd "$jet_repo"
jet_work=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-elements-clightgen.XXXXXX")
sed -e "s|@COMPCERT@|$COMPCERT|g" -e "s|@SYSROOT@|$JET_SYSROOT|g" \
  Coq/C/clightgen-linux.ini.in > "$jet_work/clightgen.ini"
"$COMPCERT/clightgen" -conf "$jet_work/clightgen.ini" \
  -U__clang__ -U__clang_major__ -U__clang_minor__ \
  -std=c11 -normalize -fstruct-passing -DPRODUCTION \
  -IC -IC/include -o "${1:-Coq/C/jets_elements.v}" Coq/C/jet_elements_translation_unit.c
printf 'Elements clightgen configuration retained at %s\n' "$jet_work/clightgen.ini"
