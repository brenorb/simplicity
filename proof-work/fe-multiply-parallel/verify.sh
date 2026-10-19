#!/usr/bin/env bash
# Fresh, isolated verification of the parallel field-multiplication proofs.
#
#   bash proof-work/fe-multiply-parallel/verify.sh OUT [TARGET_MODULE...]
#
# OUT must be a new or empty directory outside the repository. The script
#   1. checks the original-target guard against 91d89bac (C, Haskell, Coq/Simplicity);
#   2. rebuilds the pinned CompCert/VST dependencies into OUT/deps (jet-deps.sh;
#      set JET_SRC_CACHE to a directory holding the pinned tarballs to avoid a
#      download; their checksums are verified by jet-deps.sh);
#   3. exports the committed HEAD into OUT/tree (no .vo files) and materializes
#      the pinned field-negation sources and the archived jet_parallel_fe_*
#      modules (modules/) after checking their manifest hashes;
#   4. builds the dependency closure of the targets from scratch;
#   5. prints full theorem types and Print Assumptions of the public results;
#   6. runs coqchk recursively over the targets' whole dependency closure.
# Every step's exit status is recorded in OUT/STATUS.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git -C "$HERE" rev-parse --show-toplevel)
OUT=${1:?usage: verify.sh OUT [TARGET...]}; shift
TARGETS=("$@")
[ ${#TARGETS[@]} -gt 0 ] || TARGETS=(C.jet_parallel_fe_mul_local)
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
[ -z "$(ls -A "$OUT")" ] || { echo "OUT must be empty" >&2; exit 2; }
case "$OUT" in "$REPO"*) echo "OUT must be outside the repository" >&2; exit 2;; esac
ulimit -s 65520 2>/dev/null || true
status() { echo "$1 $2" >> "$OUT/STATUS"; }

REV=$(git -C "$REPO" rev-parse HEAD)
echo "revision $REV" > "$OUT/STATUS"
git -C "$REPO" status --porcelain -- C Haskell Coq/Simplicity > "$OUT/guard-worktree.txt"
git -C "$REPO" diff --quiet 91d89bac "$REV" -- C Haskell Coq/Simplicity ':(exclude)C/test.c'
status guard 0

export JET_DEPS="$OUT/deps"; mkdir -p "$JET_DEPS/src"
if [ -n "${JET_SRC_CACHE:-}" ]; then cp "$JET_SRC_CACHE"/compcert-3.14.tar.gz "$JET_SRC_CACHE"/vst-2.14.tar.gz "$JET_DEPS/src/"; fi
set +e; bash "$REPO/Coq/jet-deps.sh" > "$OUT/deps.log" 2>&1; rc=$?; set -e
status deps $rc; [ $rc -eq 0 ] || exit $rc

mkdir -p "$OUT/tree"
git -C "$REPO" archive "$REV" | tar -x -C "$OUT/tree"
# Archived: the proof modules live in modules/ as .v.source (see ARCHIVE.md).
# A source already present in the export must be byte-identical to the pin.
python3 -I - "$OUT/tree/Coq/C" "$HERE/negate-dependency/fe-negate-manifest.json" "$HERE/modules/modules-manifest.json" <<'PY'
import hashlib, json, os, sys
dst = sys.argv[1]
for manifest in sys.argv[2:]:
    src = os.path.dirname(manifest)
    m = json.load(open(manifest))
    n = same = 0
    for f in m['files']:
        if not f['path'].endswith('.v.source'):
            continue
        data = open(os.path.join(src, f['path']), 'rb').read()
        if hashlib.sha256(data).hexdigest() != f['sha256']:
            sys.exit('hash mismatch: ' + f['path'])
        out = os.path.join(dst, f['materialized_name'])
        if os.path.exists(out):
            if open(out, 'rb').read() != data:
                sys.exit('refusing to overwrite differing ' + out)
            same += 1
            continue
        open(out, 'wb').write(data); n += 1
    print(os.path.basename(manifest), 'materialized', n, 'already identical', same)
PY
status materialize 0

cd "$OUT/tree/Coq"
flags=()
for d in lib common x86_64 x86 cfrontend export; do flags+=(-R "$JET_DEPS/compcert-3.14/$d" "compcert.$d"); done
flags+=(-R "$JET_DEPS/compcert-3.14/flocq" Flocq)
for d in msl sepcomp veric zlist floyd progs64 concurrency atomics; do flags+=(-Q "$JET_DEPS/vst-2.14/$d" "VST.$d"); done
flags+=(-Q "$JET_DEPS/vst-2.14/sha" sha)
find . -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' | grep -q . && { echo "stale objects in export" >&2; exit 3; }
{ cat _CoqProject.jets; ls C/*.v | grep -vxF -f <(grep '^C/' _CoqProject.jets); } > _CoqProject.verify
coq_makefile -f _CoqProject.verify "${flags[@]}" -o VerifyMakefile > /dev/null
vos=(); for t in "${TARGETS[@]}"; do vos+=("${t#C.}"); done
vos=("${vos[@]/#/C/}"); vos=("${vos[@]/%/.vo}")
set +e; ( time make -f VerifyMakefile -j"${JOBS:-8}" "${vos[@]}" ) > "$OUT/build.log" 2>&1; rc=$?; set -e
status build $rc; [ $rc -eq 0 ] || exit $rc

mods=$(cd C && ls jet_parallel_fe_*.v | sed 's/\.v$//' | sort)
{
  for t in $mods; do echo "Require C.$t."; done
  echo "Require C.jet_secp_normalize_local C.jet_secp_negate_literal_contract C.jet_parallel_fe_sqr_field."
  echo "Print C.jet_secp_normalize_local.secp_jet_local_spec."
  echo "Print C.jet_secp_negate_literal_contract.literal_fe_multiply."
  echo "Print C.jet_secp_negate_literal_contract.literal_fe_normalize512."
  echo "Print C.jet_parallel_fe_sqr_field.literal_fe_square."
  for t in $mods; do
    for thm in $(grep -oE '^(Theorem|Lemma) [A-Za-z0-9_]+' "C/$t.v" | awk '{print $2}'); do
      echo "About C.$t.$thm."; echo "Print Assumptions C.$t.$thm."
    done
  done
} > "$OUT/Report.v"
set +e; coqc -Q Simplicity Simplicity -R C C "${flags[@]}" "$OUT/Report.v" > "$OUT/report.log" 2>&1; rc=$?; set -e
status report $rc; [ $rc -eq 0 ] || exit $rc

set +e; ( time coqchk -silent -o -Q Simplicity Simplicity -R C C "${flags[@]}" "${TARGETS[@]}" ) > "$OUT/coqchk.log" 2>&1; rc=$?; set -e
status coqchk $rc

( cd "$OUT/tree" && find Coq/C -name 'jet_parallel_fe_*.v' -o -name 'jets_secp.v' | sort | xargs shasum -a 256
  shasum -a 256 C/jets-secp256k1.c C/secp256k1/field_5x52_int128_impl.h C/secp256k1/field_5x52_impl.h \
    C/secp256k1/int128_struct_impl.h Haskell/Core/Simplicity/Programs/LibSecp256k1.hs \
    Haskell/Core/Simplicity/Programs/Arith.hs ) > "$OUT/sources.sha256"
( cd "$OUT/tree/Coq" && find C -name 'jet_parallel_fe_*.vo' | sort | xargs shasum -a 256 ) > "$OUT/objects.sha256"
exit $rc
