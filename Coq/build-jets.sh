#!/usr/bin/env bash
set -euo pipefail

# Run under the Coq 8.17.1 opam environment used to build CompCert and VST.
: "${COMPCERT:?Set COMPCERT to the built CompCert 3.14 source directory}"
: "${VST:?Set VST to the built VST 2.14 source directory}"
cd "$(dirname "$0")"

jet_flags=()
for dir in lib common x86_64 x86 cfrontend export; do
  jet_flags+=(-R "$COMPCERT/$dir" "compcert.$dir")
done
jet_flags+=(-R "$COMPCERT/flocq" Flocq)
for dir in msl sepcomp veric zlist floyd progs64 concurrency atomics; do
  jet_flags+=(-Q "$VST/$dir" "VST.$dir")
done
jet_flags+=(-Q "$VST/sha" sha)

coq_makefile -f _CoqProject.jets "${jet_flags[@]}" -o JetMakefile
make -f JetMakefile C/check_jet_assumptions.vo "$@"
