#!/usr/bin/env bash
set -euo pipefail

# Build the memcpy-linked core jet proofs in a derived tree.  The tree maps the
# accepted sources unchanged (symbolic links) under the same logical names,
# except for the generated linked programs (core and SHA translation units),
# the replacement memcpy model and the five call-site modules derived by
# linked/patch-consumers.py.
# Usage: build-linked.sh [make arguments]; the default targets are the modules of
# unconditional linked theorems and the linking theorem, not the whole project.  With --tree-only the
# derived tree is refreshed and nothing is compiled.
cd "$(dirname "$0")"
root=$PWD
tree=$root/linked/tree
mkdir -p "$tree/C"
ln -sfn "$root/Simplicity" "$tree/Simplicity"
ln -sf "$root/build-jets.sh" "$tree/build-jets.sh"
for f in "$root"/C/*.v; do
  name=$(basename "$f")
  case "$name" in
    jets.v|jets_sha.v|jet_memcpy_model.v|jet_copyBits_memcpy_exec.v|jet_copyBits_memcpy_helper.v|jet_copyBits_wide_memcpy.v|jet_sha_uchars_prep.v|jet_sha_uchars_loop.v) ;;
    *) ln -sf "$f" "$tree/C/$name" ;;
  esac
done
# The accepted program, unchanged, under a second module name: the subject of
# the CompCert linking theorem in jet_linked_program.v.
ln -sf "$root/C/jets.v" "$tree/C/jets_unlinked.v"
ln -sf "$root/C/jets_sha.v" "$tree/C/jets_sha_unlinked.v"
# Never write through a link into the accepted sources: a derived file replaces
# whatever is at the destination.
update() {
  if [[ -L "$2" ]] || ! cmp -s "$1" "$2"; then rm -f "$2"; cp "$1" "$2"; fi
}
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-linked.XXXXXX")
mkdir "$tmp/C"
python3 linked/gen-jets.py C/jets.v C/memcpy_exact.v "$tmp/C/jets.v"
python3 linked/gen-jets.py C/jets_sha.v C/memcpy_exact.v "$tmp/C/jets_sha.v"
python3 linked/patch-consumers.py C "$tmp/C"
for f in "$tmp"/C/*.v; do update "$f" "$tree/C/$(basename "$f")"; done
for f in linked/C/*.v; do
  rm -f "$tree/C/$(basename "$f")"
  ln -s "$root/$f" "$tree/C/$(basename "$f")"
done
{
  cat _CoqProject.jets
  for name in memcpy_impl jet_memcpy_impl memcpy_exact jet_memcpy_exact \
      jet_frame_constructible jet_frame_constructible_jets jet_frame_executable_registry; do
    grep -qx "C/$name.v" _CoqProject.jets || printf 'C/%s.v\n' "$name"
  done
  printf 'C/jets_unlinked.v\nC/jets_sha_unlinked.v\n'
  for f in linked/C/*.v; do
    grep -qx "C/$(basename "$f")" _CoqProject.jets || printf 'C/%s\n' "$(basename "$f")"
  done
} > "$tmp/project"
update "$tmp/project" "$tree/_CoqProject.jets"
rm -rf "$tmp"
cd "$tree"
if [[ "${1:-}" == --tree-only ]]; then exit 0; fi
# Same library load paths as build-jets.sh (shell workflow only).
JET_DEPS=${JET_DEPS:-${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}
COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14}
VST=${VST:-$JET_DEPS/vst-2.14}
if [[ ! -f "$COMPCERT/compcert.config" || ! -d "$VST/sha" ]]; then
  echo "CompCert/VST not found; run Coq/jet-deps.sh (see Coq/JET_BUILD.md)" >&2
  exit 1
fi
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
targets=0
for arg in "$@"; do [[ "$arg" == *.vo ]] && targets=1; done
if [[ $targets == 0 ]]; then
  for f in "$root"/linked/C/jet_linked_*.v "$root"/linked/C/*_linked.v; do
    name=$(basename "$f"); set -- "$@" "C/${name%.v}.vo"
  done
fi
exec make -f JetMakefile "$@"
