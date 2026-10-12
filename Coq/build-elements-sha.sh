#!/usr/bin/env bash
set -euo pipefail

# Compile the accepted SHA proof chain against the Elements translation unit.
#
# The Elements program (C/jets_elements.v, generated from a unit that
# includes sha256.c) contains every C definition the SHA proof modules
# mention with the same text as the SHA unit (checked by
# elements-sha/check-definitions.py).  In the derived tree
# Coq/elements-sha/tree the module C.jets_sha is a copy of C.jets_elements,
# all other sources are the accepted ones (symbolic links), and the SHA
# modules are recompiled.  Compiled objects of modules that do not depend on
# C.jets_sha are copied from this tree's normal build (never linked: nothing
# here may write into the accepted tree).
# Usage: build-elements-sha.sh [make arguments]; default targets: every
# C/jet_sha*.vo and the statement that the two programs are equal.
cd "$(dirname "$0")"
root=$PWD
tree=$root/elements-sha/tree
python3 elements-sha/check-definitions.py
mkdir -p "$tree/C"
ln -sfn "$root/Simplicity" "$tree/Simplicity"
ln -sf "$root/build-jets.sh" "$tree/build-jets.sh"
for f in "$root"/C/*.v; do
  name=$(basename "$f")
  [[ "$name" == jets_sha.v ]] || ln -sf "$f" "$tree/C/$name"
done
update() { if [[ -L "$2" ]] || ! cmp -s "$1" "$2"; then rm -f "$2"; cp "$1" "$2"; fi; }
update "$root/C/jets_elements.v" "$tree/C/jets_sha.v"
for f in elements-sha/C/*.v; do
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
  printf 'C/jets_elements.v\n'
  for f in elements-sha/C/*.v; do printf 'C/%s\n' "$(basename "$f")"; done
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
  # the SHA modules of the accepted project, except those about the Bitcoin
  # environment layout of the SHA unit (they do not concern the Elements unit)
  for f in "$root"/C/jet_sha*.v; do
    name=$(basename "$f")
    grep -qx "C/$name" _CoqProject.jets || continue
    case "$name" in jet_sha_indexed_exec.v|jet_sha_index_eval.v|jet_sha_steps.v) continue ;; esac
    set -- "$@" "C/${name%.v}.vo"
  done
  for f in "$root"/elements-sha/C/*.v; do name=$(basename "$f"); set -- "$@" "C/${name%.v}.vo"; done
fi
exec make -f JetMakefile "$@"
