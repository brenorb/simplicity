#!/usr/bin/env bash
# Integrated verification of the jet proofs.
#
#   check-jets.sh [--update-expected] [--ast] [--accept]
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
#      inputs and compare the core, Bitcoin, SHA and secp256k1 artifacts with committed ASTs.
# Requires Coq 8.17.1 on PATH and JET_DEPS prepared by jet-deps.sh (and
# jet-sysroot.sh for step 5; JET_SYSROOT defaults to its output directory).
set -euo pipefail
cd "$(dirname "$0")"

update=false; ast=false; build=true; accept=false
for a in "$@"; do
  case "$a" in
    --update-expected) update=true ;;
    --ast) ast=true ;;
    --no-build) build=false ;;
    --accept) accept=true ;;
    *) echo "unknown option $a" >&2; exit 2 ;;
  esac
done
if $accept; then
  if $update || ! $build; then
    echo '--accept requires a build and comparison with reviewed snapshots; no update/no-build flags' >&2
    exit 2
  fi
  ast=true
fi
[[ -n "${JET_SYSROOT:-}" ]] && ast=true
jobs=${JOBS:-$( (nproc || sysctl -n hw.ncpu) 2>/dev/null || echo 2)}
# The native checker over the symbolic-execution proofs exceeds the default
# macOS 8 MiB stack. Raise the resource limit, preserving every kernel check.
checker_stack_kib=$(ulimit -S -s)
if [[ "$checker_stack_kib" != unlimited && "$checker_stack_kib" -lt 65520 ]]; then
  if ! ulimit -S -s 65520; then
    echo 'jet verification needs a 65520 KiB stack; increase the OS hard stack limit' >&2
    exit 1
  fi
fi
echo "checker stack limit (KiB): $(ulimit -S -s)"
audit_inputs() {
  if $update; then
    python3 jet-audit-inputs.py --updating
  else
    python3 jet-audit-inputs.py
  fi
}
inputs_before=$(audit_inputs)

echo "== static checks"
python3 check-jet-source-target.py
python3 test-jet-source-target.py
python3 scan-jet-proofs.py
python3 jet-coverage.py
python3 test-jet-coverage.py
python3 check-fullshift-specification.py
python3 test-fullshift-specification.py
python3 check-secp-normalize-specification.py
python3 test-secp-normalize-specification.py
python3 check-bitcoin-primitive-identity.py
python3 test-bitcoin-primitive-identity.py
python3 test-jet-audit-inputs.py

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
  COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14} JET_SYSROOT=$JET_SYSROOT \
    bash C/check-bitcoin-jets-generation.sh
  COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14} JET_SYSROOT=$JET_SYSROOT \
    bash C/check-sha-jets-generation.sh
  COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14} JET_SYSROOT=$JET_SYSROOT \
    bash C/check-secp-jets-generation.sh
fi
inputs_after=$(audit_inputs)
if [[ "$inputs_before" != "$inputs_after" ]]; then
  echo 'audit inputs changed during verification; rerun against the final sources' >&2
  exit 1
fi
echo "audit input SHA-256: $inputs_after"
if $update; then
  echo 'candidate snapshots generated; review their diffs, then rerun --accept without update flags'
elif $accept; then
  echo 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, four ASTs)'
elif ! $build; then
  echo 'jet artifact checks passed (--no-build; current sources were not rebuilt by this run)'
elif ! $ast; then
  echo 'jet proof checks passed (AST regeneration not run; use --accept for acceptance)'
else
  echo 'all jet checks passed'
fi
