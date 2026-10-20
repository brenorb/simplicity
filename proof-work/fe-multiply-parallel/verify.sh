#!/usr/bin/env bash
# Build and kernel-check both archived alternatives in a new external directory.
# Requires the same Coq 8.17.1 and JET_DEPS as Coq/build-jets.sh.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git -C "$HERE" rev-parse --show-toplevel)
OUT=${1:?usage: verify.sh NEW_EXTERNAL_DIRECTORY}
[[ ! -e "$OUT" ]] || { echo 'output directory must not exist' >&2; exit 2; }
# Resolve the parent before creating anything, including paths containing '..'.
OUT=$(python3 -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve())' "$OUT")
case "$OUT" in "$REPO"|"$REPO"/*) echo 'output must be outside the repository' >&2; exit 2;; esac
ulimit -s 65520
REV=$(git -C "$REPO" rev-parse HEAD)
git -C "$REPO" diff --quiet 91d89bac "$REV" -- C Haskell Coq/Simplicity ':(exclude)C/test.c'
mkdir -p "$OUT"
git -C "$REPO" archive "$REV" | tar -x -C "$OUT"
python3 - "$OUT" <<'PY'
from pathlib import Path
import sys
root = Path(sys.argv[1])
modules = sorted((root / 'proof-work/fe-multiply-parallel/modules').glob('*.v.source'))
if len(modules) != 13:
    raise SystemExit('expected all 13 alternative proof modules')
for source in modules:
    target = root / 'Coq/C' / source.name.removesuffix('.source')
    if target.exists():
        raise SystemExit(f'refusing to overwrite {target}')
    target.write_bytes(source.read_bytes())
for project in ('_CoqProject', '_CoqProject.jets'):
    with (root / 'Coq' / project).open('a') as f:
        f.write('\n' + '\n'.join('C/' + p.name.removesuffix('.source') for p in modules) + '\n')
PY
cd "$OUT"
JET_TARGETS='C/jet_parallel_fe_mul_local.vo C/jet_parallel_fe_sqr_local.vo' \
  bash Coq/build-jets.sh -j"${JOBS:-4}"
cat > "$OUT/AlternativeTypes.v" <<'COQ'
Require C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local.
About C.jet_parallel_fe_mul_local.fe_multiply_literal_local_spec.
Print Assumptions C.jet_parallel_fe_mul_local.fe_multiply_literal_local_spec.
About C.jet_parallel_fe_sqr_local.fe_square_literal_local_spec.
Print Assumptions C.jet_parallel_fe_sqr_local.fe_square_literal_local_spec.
COQ
bash Coq/build-jets.sh --coqc -q "$OUT/AlternativeTypes.v"
bash Coq/build-jets.sh --coqchk -silent -o \
  C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local
