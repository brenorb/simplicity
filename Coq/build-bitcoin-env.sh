#!/usr/bin/env bash
set -euo pipefail

# Compile the accepted SHA-unit proof chain against the environment unit: the
# SHA translation unit followed by bitcoin/env.c (C/jets_bitcoin_env.v).
#
# Every function and global of the SHA unit has the same generated text in
# the environment unit (bitcoin-env/check-definitions.py).  In the derived
# tree Coq/bitcoin-env/tree the module C.jets_sha is a copy of
# C.jets_bitcoin_env, all other sources are the accepted ones (symbolic
# links), and every module that depends on C.jets_sha is recompiled.
# Compiled objects of other modules are copied from this tree's normal build
# (never linked: nothing here may write into the accepted tree).
# Usage: build-bitcoin-env.sh [make arguments]; default targets: the modules
# of bitcoin-env/C and what they require.
cd "$(dirname "$0")"
root=$PWD
tree=$root/bitcoin-env/tree
python3 bitcoin-env/check-definitions.py
mkdir -p "$tree/C"
ln -sfn "$root/Simplicity" "$tree/Simplicity"
ln -sf "$root/build-jets.sh" "$tree/build-jets.sh"
for f in "$root"/C/*.v; do
  name=$(basename "$f")
  [[ "$name" == jets_sha.v ]] || ln -sf "$f" "$tree/C/$name"
done
update() { if [[ -L "$2" ]] || ! cmp -s "$1" "$2"; then rm -f "$2"; cp "$1" "$2"; fi; }
update "$root/C/jets_bitcoin_env.v" "$tree/C/jets_sha.v"
for f in bitcoin-env/C/*.v; do
  [[ -e "$f" ]] || continue
  rm -f "$tree/C/$(basename "$f")"; ln -s "$root/$f" "$tree/C/$(basename "$f")"
done
# compiled objects of the normal tree, as copies, where absent
for f in "$root"/C/*.vo; do
  base=$(basename "${f%.vo}")
  [[ "$base" == jets_sha ]] && continue
  if [[ ! -e "$tree/C/$base.vo" ]]; then
    for ext in vo vos vok glob; do
      [[ -e "$root/C/$base.$ext" ]] && cp -p "$root/C/$base.$ext" "$tree/C/$base.$ext"
    done
  fi
done
# start-up invariant modules: only when the archived prerequisites have been
# extracted by build-startup.sh (startup/prereq is not part of this branch)
startup=0
if [[ -e startup/prereq/jet_clight_forward.v && -e startup/prereq/jet_sha_initial_globals.v ]]; then
  startup=1
  mkdir -p "$tree/startup/prereq" "$tree/startup/proofs" "$tree/startup/env"
  for name in jet_clight_forward jet_sha_initial_globals; do
    ln -sf "$root/startup/prereq/$name.v" "$tree/startup/prereq/$name.v"
  done
  for name in jet_sha_startup_globals jet_sha_startup_state; do
    ln -sf "$root/startup/proofs/$name.v" "$tree/startup/proofs/$name.v"
  done
  for f in bitcoin-env/startup/*.v; do ln -sf "$root/$f" "$tree/startup/env/$(basename "$f")"; done
fi
{
  cat _CoqProject.jets
  printf 'C/jets_bitcoin_env.v\n'
  for f in bitcoin-env/C/*.v; do [[ -e "$f" ]] && printf 'C/%s\n' "$(basename "$f")"; done
  if [[ $startup == 1 ]]; then
    printf -- '-Q startup/prereq JetStartupReview\n-Q startup/proofs JetStartup\n-Q startup/env BitcoinEnvStartup\n'
    printf 'startup/prereq/jet_clight_forward.v\nstartup/prereq/jet_sha_initial_globals.v\n'
    printf 'startup/proofs/jet_sha_startup_globals.v\nstartup/proofs/jet_sha_startup_state.v\n'
    for f in bitcoin-env/startup/*.v; do printf 'startup/env/%s\n' "$(basename "$f")"; done
  fi
} > "$tree/_CoqProject.jets.new"
update "$tree/_CoqProject.jets.new" "$tree/_CoqProject.jets"; rm -f "$tree/_CoqProject.jets.new"
cd "$tree"
JET_DEPS=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14}
VST=${VST:-$JET_DEPS/vst-2.14}
jet_flags=()
for dir in lib common x86_64 x86 cfrontend export; do jet_flags+=(-R "$COMPCERT/$dir" "compcert.$dir"); done
jet_flags+=(-R "$COMPCERT/flocq" Flocq)
for dir in msl sepcomp veric zlist floyd progs64 concurrency atomics; do jet_flags+=(-Q "$VST/$dir" "VST.$dir"); done
jet_flags+=(-Q "$VST/sha" sha)
coq_makefile -f _CoqProject.jets "${jet_flags[@]}" -o JetMakefile
ulimit -s 65520 2>/dev/null || true
targets=0
for arg in "$@"; do [[ "$arg" == *.vo ]] && targets=1; done
if [[ $targets == 0 ]]; then
  for f in "$root"/bitcoin-env/C/*.v; do
    [[ -e "$f" ]] || continue
    name=$(basename "$f"); set -- "$@" "C/${name%.v}.vo"
  done
  if [[ $startup == 1 ]]; then
    for f in "$root"/bitcoin-env/startup/*.v; do name=$(basename "$f"); set -- "$@" "startup/env/${name%.v}.vo"; done
  fi
fi
exec make -f JetMakefile "$@"
