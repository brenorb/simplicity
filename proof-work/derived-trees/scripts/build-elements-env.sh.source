#!/usr/bin/env bash
set -euo pipefail

# Compile the SHA proof modules needed for the Elements environment builders
# against the Elements environment unit (C/jets_elements_env.v: core jets,
# sha256.c, elements/ops.c, elements/env.c).
#
# The C definitions those modules mention have the same generated text there
# as in the SHA unit (elements-env/check-definitions.py).  In the derived
# tree Coq/elements-env/tree the module C.jets_sha is a copy of
# C.jets_elements_env, all other sources are the accepted ones (symbolic
# links) plus the Elements tapleaf modules of elements-sha/C and the
# generated ports of elements-env/C; what the targets need is recompiled.
# Compiled objects of other modules are copied from this tree's normal build
# (never linked: nothing here may write into the accepted tree).
# Usage: build-elements-env.sh [make arguments]; default targets: the modules
# of elements-env/C and what they require.
cd "$(dirname "$0")"
root=$PWD
tree=$root/elements-env/tree
python3 elements-env/check-definitions.py
mkdir -p "$tree/C"
ln -sfn "$root/Simplicity" "$tree/Simplicity"
ln -sf "$root/build-jets.sh" "$tree/build-jets.sh"
for f in "$root"/C/*.v; do
  name=$(basename "$f")
  [[ "$name" == jets_sha.v ]] || ln -sf "$f" "$tree/C/$name"
done
update() { if [[ -L "$2" ]] || ! cmp -s "$1" "$2"; then rm -f "$2"; cp "$1" "$2"; fi; }
update "$root/C/jets_elements_env.v" "$tree/C/jets_sha.v"
extra=(elements-sha/C/jet_elements_tap_tags.v elements-sha/C/jet_elements_make_tapleaf_exec.v elements-env/C/*.v)
for f in "${extra[@]}"; do
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
{
  cat _CoqProject.jets
  printf 'C/jets_elements_env.v\n'
  # libc contracts used by the Elements builders (not in the shared project file)
  for name in jet_memcmp_model jet_memcmp_words; do
    grep -qx "C/$name.v" _CoqProject.jets || printf 'C/%s.v\n' "$name"
  done
  for f in "${extra[@]}"; do printf 'C/%s\n' "$(basename "$f")"; done
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
  for f in "$root"/elements-env/C/*.v; do
    name=$(basename "$f"); set -- "$@" "C/${name%.v}.vo"
  done
fi
exec make -f JetMakefile "$@"
