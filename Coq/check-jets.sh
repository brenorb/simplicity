#!/usr/bin/env bash
# Integrated verification of the jet proofs.
#
#   check-jets.sh [--update-expected] [--ast]
#
# Steps (each fails the script):
#   1. static checks: no Axiom/Parameter/Admitted in the jet sources; every jet
#      module of _CoqProject.jets is also listed in the normal _CoqProject;
#   2. build every module of _CoqProject.jets (build-jets.sh);
#   3. coqchk on every module that contains a public theorem
#      (C/jet_public_theorems.txt), compared with the recorded library-level
#      axiom list C/jet_coqchk_axioms.expected;
#   4. the per-theorem assumption gate (audit-jet-assumptions.sh);
#   5. with --ast (or JET_SYSROOT set): regenerate the C AST with the pinned
#      inputs and compare it with the committed C/jets.v.
# Requires Coq 8.17.1 on PATH and JET_DEPS prepared by jet-deps.sh (and
# jet-sysroot.sh for step 5; JET_SYSROOT defaults to its output directory).
set -euo pipefail
cd "$(dirname "$0")"

update=false; ast=false; build=true
for a in "$@"; do
  case "$a" in
    --update-expected) update=true ;;
    --ast) ast=true ;;
    --no-build) build=false ;;
    *) echo "unknown option $a" >&2; exit 2 ;;
  esac
done
[[ -n "${JET_SYSROOT:-}" ]] && ast=true
jobs=${JOBS:-$( (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 2)}

echo "== static checks"
python3 scan-jet-proofs.py

missing=$(comm -23 <(grep -E '^C/jets?[_.]' _CoqProject.jets | sort -u) \
                   <(grep -E '^C/jets?[_.]' _CoqProject | sort -u) || true)
if [[ -n "$missing" ]]; then
  echo "jet modules missing from _CoqProject:" >&2; echo "$missing" >&2; exit 1
fi
for m in $(awk '!/^#/ && NF==2 {print $1}' C/jet_public_theorems.txt | sort -u); do
  f=${m//./\/}.v
  grep -qx "$f" _CoqProject.jets || { echo "$f not in _CoqProject.jets" >&2; exit 1; }
done

if $build; then
  echo "== build (make -j$jobs)"
  bash build-jets.sh -j"$jobs"
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/jet-check.XXXXXX")
trap 'rm -rf "$work"' EXIT
echo "== coqchk"
mods=$(awk '!/^#/ && NF==2 {print $1}' C/jet_public_theorems.txt | sort -u | tr '\n' ' ')
# shellcheck disable=SC2086
if ! bash build-jets.sh --coqchk -silent -o $mods > "$work/coqchk.out" 2>&1; then
  cat "$work/coqchk.out" >&2
  exit 1
fi
axioms=$(awk '/^\* Axioms:/{f=1;next} f&&NF==0{exit} f{print $1}' "$work/coqchk.out" | sort)
grep -q 'Constants/Inductives relying on type-in-type: <none>' "$work/coqchk.out"
grep -q 'unsafe (co)fixpoints: <none>' "$work/coqchk.out"
grep -q 'positivity is assumed: <none>' "$work/coqchk.out"
if $update; then printf '%s\n' "$axioms" > C/jet_coqchk_axioms.expected
elif ! diff <(printf '%s\n' "$axioms") C/jet_coqchk_axioms.expected; then
  echo "coqchk library-level axioms differ from C/jet_coqchk_axioms.expected" >&2; exit 1
fi
echo "coqchk passed on $(echo $mods | wc -w | tr -d ' ') modules"

echo "== assumption gate"
if $update; then bash audit-jet-assumptions.sh --update; else bash audit-jet-assumptions.sh; fi

echo "== public contract gate"
if $update; then bash audit-jet-contracts.sh --update; else bash audit-jet-contracts.sh; fi

echo "== gate negative tests"
python3 test-jet-gates.py

if $ast; then
  echo "== AST regeneration"
  : "${JET_DEPS:=${XDG_CACHE_HOME:-$HOME/.cache}/simplicity-jet-deps}"
  JET_SYSROOT=${JET_SYSROOT:-$JET_DEPS/sysroot-glibc-2.36}
  if [[ ! -d "$JET_SYSROOT/usr/include" ]]; then
    echo "glibc sysroot not found at $JET_SYSROOT; run Coq/jet-sysroot.sh" >&2; exit 1
  fi
  COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14} JET_SYSROOT=$JET_SYSROOT \
    bash C/check-jets-generation.sh
fi
echo "all jet checks passed"
