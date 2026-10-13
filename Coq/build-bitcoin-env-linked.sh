#!/usr/bin/env bash
set -euo pipefail

# The environment-unit proofs (bitcoin-env/C) against the memcpy-linked
# environment unit: C/jets_bitcoin_env.v with the external declaration of
# memcpy replaced by the internal definition generated from
# jet_memcpy_exact.c (linked/gen-jets.py, the same derivation as the linked
# SHA unit).  The derived tree bitcoin-env-linked/tree starts from the
# linked tree (linked/tree: linked core program, replacement memcpy model,
# patched call-site modules and their compiled objects, as copies); only the
# module C.jets_sha differs, and everything that depends on it is
# recompiled.  All proof sources are compiled unchanged.
# Usage: build-bitcoin-env-linked.sh [make arguments]; default targets: the
# modules of bitcoin-env-linked/C.  Requires a built linked tree
# (build-linked.sh).
cd "$(dirname "$0")"
root=$PWD
base=$root/linked/tree
tree=$root/bitcoin-env-linked/tree
[[ -e "$base/C/jets_sha.vo" ]] || { echo "build the linked tree first (bash build-linked.sh)" >&2; exit 1; }
python3 bitcoin-env/check-definitions.py
mkdir -p "$tree/C"
ln -sfn "$root/Simplicity" "$tree/Simplicity"
ln -sf "$root/build-jets.sh" "$tree/build-jets.sh"
update() { if [[ -L "$2" ]] || ! cmp -s "$1" "$2"; then rm -f "$2"; cp "$1" "$2"; fi; }
for f in "$base"/C/*.v; do
  name=$(basename "$f")
  [[ "$name" == jets_sha.v ]] && continue
  if [[ -L "$f" ]]; then ln -sf "$(readlink "$f")" "$tree/C/$name"; else update "$f" "$tree/C/$name"; fi
done
# accepted sources added after the linked tree was laid out
for f in "$root"/C/*.v; do
  name=$(basename "$f")
  [[ "$name" == jets_sha.v || -e "$tree/C/$name" ]] || ln -sf "$f" "$tree/C/$name"
done
tmp=$(mktemp -d "${TMPDIR:-/tmp}/simplicity-bitcoin-env-linked.XXXXXX")
python3 linked/gen-jets.py C/jets_bitcoin_env.v C/memcpy_exact.v "$tmp/jets_sha.v"
update "$tmp/jets_sha.v" "$tree/C/jets_sha.v"
for f in bitcoin-env/C/*.v bitcoin-env-linked/C/*.v; do
  [[ -e "$f" ]] || continue
  rm -f "$tree/C/$(basename "$f")"; ln -s "$root/$f" "$tree/C/$(basename "$f")"
done
# compiled objects of the linked tree, as copies, where absent
for f in "$base"/C/*.vo; do
  b=$(basename "${f%.vo}")
  [[ "$b" == jets_sha ]] && continue
  if [[ ! -e "$tree/C/$b.vo" ]]; then
    for ext in vo vos vok glob; do
      [[ -e "$base/C/$b.$ext" ]] && cp -p "$base/C/$b.$ext" "$tree/C/$b.$ext"
    done
  fi
done
{
  cat "$base/_CoqProject.jets"
  for f in bitcoin-env/C/*.v bitcoin-env-linked/C/*.v; do
    [[ -e "$f" ]] || continue
    grep -qx "C/$(basename "$f")" "$base/_CoqProject.jets" || printf 'C/%s\n' "$(basename "$f")"
  done
  for name in jets_bitcoin_env; do printf 'C/%s.v\n' "$name"; done
} > "$tmp/project"
update "$tmp/project" "$tree/_CoqProject.jets"
rm -rf "$tmp"
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
  for f in "$root"/bitcoin-env-linked/C/*.v; do
    [[ -e "$f" ]] || continue
    name=$(basename "$f"); set -- "$@" "C/${name%.v}.vo"
  done
fi
exec make -f JetMakefile "$@"
