#!/usr/bin/env bash
set -euo pipefail

# Build (or check) the jet proofs.  Run with Coq 8.17.1 on PATH.
# Dependencies come from JET_DEPS (default ~/.cache/simplicity-jet-deps), which
# jet-deps.sh populates; COMPCERT and VST override the two source trees.
JET_DEPS=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14}
VST=${VST:-$JET_DEPS/vst-2.14}
if [[ ! -f "$COMPCERT/compcert.config" || ! -d "$VST/sha" ]]; then
  printf 'CompCert/VST not found under %s; run Coq/jet-deps.sh (see Coq/JET_BUILD.md)\n' "$JET_DEPS" >&2
  exit 1
fi
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

# Reuse the exact project load paths for a short proof/debug/check cycle.
# These modes do not rebuild dependencies; run the default build first.
case "${1:-}" in
  --coqc|--coqtop|--coqchk)
    jet_tool=${1#--}
    shift
    exec "$jet_tool" -Q Simplicity Simplicity -R C C "${jet_flags[@]}" "$@"
    ;;
esac

project=_CoqProject.jets
makefile=JetMakefile
if [[ "${1:-}" == --regression ]]; then
  project=_CoqProject.jets-regression
  makefile=JetRegressionMakefile
  shift
fi
coq_makefile -f "$project" "${jet_flags[@]}" -o "$makefile"
make -f "$makefile" all "$@"
