#!/usr/bin/env bash
# Integrated verification of the jet proofs.
#
#   check-jets.sh [--update-expected] [--ast] [--accept] [--jets=NAME,...]
#
# --jets scopes the build, kernel check and snapshot gates to the listed jets
# (C/jet_coverage.tsv names) and their dependency closure, so an unrelated
# broken module does not block them. Static checks and AST regeneration stay
# global. Without --jets every module is checked.
#
# Steps (each fails the script):
#   1. static checks: no Axiom/Parameter/Admitted in the jet sources; every jet
#      module of _CoqProject.jets is also listed in the normal _CoqProject;
#   2. build every module of _CoqProject.jets (build-jets.sh);
#   3. coqchk on every module of _CoqProject.jets, compared with the recorded
#      library-level axiom list C/jet_coqchk_axioms.expected;
#   4. the per-theorem assumption gate (audit-jet-assumptions.sh);
#   5. with --ast (or JET_SYSROOT set): regenerate the C AST with the pinned
#      inputs and compare core, Bitcoin, SHA, secp256k1 and Elements artifacts.
# Requires Coq 8.17.1 on PATH and JET_DEPS prepared by jet-deps.sh (and
# jet-sysroot.sh for step 5; JET_SYSROOT defaults to its output directory).
set -euo pipefail
cd "$(dirname "$0")"
# Selection is controlled only by --jets, never by a caller's stale shell state.
unset JET_ONLY_MODULES JET_TARGETS

update=false; ast=false; build=true; accept=false; jets=""
for a in "$@"; do
  case "$a" in
    --update-expected) update=true ;;
    --ast) ast=true ;;
    --no-build) build=false ;;
    --accept) accept=true ;;
    --jets=*) jets=${a#--jets=} ;;
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

# Source and mutation checks are independent and write only to temporary trees.
# Run each unchanged command, keep its own exit status, and print logs in order.
work=$(mktemp -d "${TMPDIR:-/tmp}/jet-check.XXXXXX")
trap 'rm -rf "$work"' EXIT
static_started=0; static_next=0; static_failed=0
static_pids=(); static_labels=()
static_wait_one() {
  local slot=$static_next
  if ! wait "${static_pids[$slot]}"; then static_failed=1; fi
  printf '== source check: %s\n' "${static_labels[$slot]}"
  cat "$work/static-$slot.log"
  static_next=$((static_next + 1))
}
static_check() {
  local slot=$static_started
  static_labels[$slot]=$(printf '%q ' "$@")
  "$@" > "$work/static-$slot.log" 2>&1 &
  static_pids[$slot]=$!
  static_started=$((static_started + 1))
  if (( static_started - static_next >= jobs )); then static_wait_one; fi
}
echo "== static checks"
static_check python3 check-jet-source-target.py
static_check python3 test-jet-source-target.py
static_check python3 scan-jet-proofs.py
static_check python3 jet-coverage.py
static_check python3 test-jet-coverage.py
static_check python3 elements-version-review/check-version-source.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 elements-version-review/test-version-source.py "${JET_C_REPO:-..}" .
static_check python3 elements-version-review/check-getters-source.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 elements-version-review/test-getters-source.py "${JET_C_REPO:-..}" .
static_check python3 elements-count-review/check-source.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 elements-count-review/test-source.py "${JET_C_REPO:-..}" .
static_check python3 elements-sequence-review/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_sequence_literal.v
static_check python3 elements-sequence-review/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_sequence_literal.v
static_check python3 elements-current-sequence/check-source.py --repo "${JET_C_REPO:-..}" --coq . --sequence C/jet_elements_sequence_literal.v --literal C/jet_elements_current_sequence_literal.v
static_check python3 elements-current-sequence/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_sequence_literal.v C/jet_elements_current_sequence_literal.v
static_check python3 elements-tapleaf-literal/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_tapleaf_literal.v
static_check python3 elements-tapleaf-literal/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_tapleaf_literal.v
static_check python3 elements-hash-literal/check-source.py --repo "${JET_C_REPO:-..}" --coq . --helper C/jet_haskell_hash_word.v --endpoint C/jet_elements_hash_literal.v
static_check python3 elements-hash-literal/test-source.py "${JET_C_REPO:-..}" . C/jet_haskell_hash_word.v C/jet_elements_hash_literal.v
static_check python3 elements-finality/check-source.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 elements-finality/test-source.py "${JET_C_REPO:-..}" .
static_check python3 elements-lock/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_lock_literal.v
static_check python3 elements-lock/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_lock_literal.v
static_check python3 elements-check-lock/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_check_lock_literal.v --transport C/jet_application_partial_transport.v
static_check python3 elements-check-lock/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_check_lock_literal.v C/jet_application_partial_transport.v
static_check python3 elements-pegin/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_pegin_literal.v
static_check python3 elements-pegin/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_pegin_literal.v
static_check python3 elements-script-hash/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_script_hash_literal.v
static_check python3 elements-script-hash/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_script_hash_literal.v
static_check python3 elements-issuance-proof/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_issuance_proof_literal.v
static_check python3 elements-issuance-proof/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_issuance_proof_literal.v
static_check python3 elements-annex-hash/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_optional_digest_literal.v
static_check python3 elements-annex-hash/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_optional_digest_literal.v
static_check python3 elements-issuance-digest/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_issuance_digest_literal.v
static_check python3 elements-issuance-digest/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_issuance_digest_literal.v
static_check python3 elements-outpoint-output/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_indexed_literal.v
static_check python3 elements-outpoint-output/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_indexed_literal.v
static_check python3 elements-output-proof/check-source.py --repo "${JET_C_REPO:-..}" --coq . --literal C/jet_elements_output_proof_literal.v
static_check python3 elements-output-proof/test-source.py "${JET_C_REPO:-..}" . C/jet_elements_output_proof_literal.v
static_check python3 elements-tap-getters/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-tap-getters/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-lbtc-asset/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-lbtc-asset/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-legacy-lock/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-legacy-lock/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-legacy-check/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-legacy-check/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-output-nonce/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-output-nonce/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-asset-literal/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-asset-literal/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-amount-literal/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-amount-literal/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-issuance-amount-literal/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-issuance-amount-literal/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-token-amount-complete/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-token-amount-complete/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-txid-literal/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-txid-literal/test-source.py "${JET_C_REPO:-..}"
static_check python3 elements-null-data-source/check-source.py "${JET_C_REPO:-..}"
static_check python3 elements-null-data-source/test-source.py "${JET_C_REPO:-..}"
static_check python3 check-fullshift-specification.py
static_check python3 test-fullshift-specification.py
static_check python3 check-secp-normalize-specification.py
static_check python3 test-secp-normalize-specification.py
static_check python3 check-secp-predicates-specification.py
static_check python3 test-secp-predicates-specification.py
for gate in negate-wiring recursive-ports literal-ports foundations; do
  candidate_ports=C
  if [[ "$gate" == recursive-ports ]]; then candidate_ports=negate-review; fi
  python3 "negate-review/check-$gate.py" --repo "${JET_C_REPO:-..}" --candidates "$candidate_ports"
  python3 "negate-review/test-$gate.py" --repo "${JET_C_REPO:-..}" --candidates "$candidate_ports"
done
static_check python3 add-review/check-add-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 add-review/test-add-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 infinity-review/check-infinity-wiring.py --repo "${JET_C_REPO:-..}" --candidates C
static_check python3 infinity-review/test-infinity-wiring.py --repo "${JET_C_REPO:-..}" --candidates C
static_check python3 predicate-review/check-gej-predicate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 predicate-review/test-gej-predicate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 gej-negate-review/check-gej-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 gej-negate-review/test-gej-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 ge-negate-review/check-ge-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 ge-negate-review/test-ge-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C
static_check python3 scalar-review/check-literal.py --repo "${JET_C_REPO:-..}" --source C --coq .
static_check python3 scalar-review/test-literal.py "${JET_C_REPO:-..}" C .
static_check python3 scalar-review/test-scalar-ports.py "${JET_C_REPO:-..}" C .
static_check python3 scalar-integration-review/check-normalize-public.py --repo "${JET_C_REPO:-..}" --source C --dependencies C --coq .
static_check python3 scalar-integration-review/test-normalize-public.py "${JET_C_REPO:-..}" C C .
static_check python3 scalar-integration-review/check-negate-ports.py --repo "${JET_C_REPO:-..}" --source C --dependencies C --coq .
static_check python3 scalar-integration-review/test-negate-ports.py "${JET_C_REPO:-..}" C C .
static_check python3 scalar-integration-review/check-negate-public.py --repo "${JET_C_REPO:-..}" --source C --dependencies C --coq .
static_check python3 scalar-integration-review/test-negate-public.py "${JET_C_REPO:-..}" C C .
static_check python3 scalar-add-review/check-add-bridge.py --repo "${JET_C_REPO:-..}" --source C --coq .
static_check python3 scalar-add-review/test-add-bridge.py "${JET_C_REPO:-..}" C .
static_check python3 scalar-add-review/check-add-public.py --repo "${JET_C_REPO:-..}" --source C --coq .
static_check python3 scalar-add-review/test-add-public.py "${JET_C_REPO:-..}" C .
static_check python3 scalar-multiply-review/check-multiply-public.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 scalar-multiply-review/test-multiply-public.py "${JET_C_REPO:-..}" .
static_check python3 scalar-square-review/check-square-public.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 scalar-square-review/test-square-public.py "${JET_C_REPO:-..}" .
static_check python3 scalar-lambda-integration/check-lambda-public.py --repo "${JET_C_REPO:-..}" --coq .
static_check python3 scalar-lambda-integration/test-lambda-public.py "${JET_C_REPO:-..}" .
static_check python3 check-bitcoin-primitive-identity.py
static_check python3 test-bitcoin-primitive-identity.py
static_check python3 test-jet-audit-inputs.py

while (( static_next < static_started )); do static_wait_one; done
if (( static_failed )); then
  echo 'source or mutation checks failed; proof acceptance stopped' >&2
  exit 1
fi

missing=$(comm -23 <(grep -E '^C/jets?[_.]' _CoqProject.jets | sort -u) \
                   <(grep -E '^C/jets?[_.]' _CoqProject | sort -u) || true)
if [[ -n "$missing" ]]; then
  echo "jet modules missing from _CoqProject:" >&2; echo "$missing" >&2; exit 1
fi
if [[ -n "$jets" ]]; then
  roots=$(python3 - "$jets" <<'PY'
import sys
want = [j for j in sys.argv[1].split(",") if j]
rows = {}
for line in open("C/jet_coverage.tsv"):
    parts = line.split()
    if len(parts) == 3 and not line.startswith("#"):
        rows[parts[0]] = parts[1]
missing = [j for j in want if j not in rows]
if missing:
    sys.exit("jets not in C/jet_coverage.tsv: " + ", ".join(missing))
print(" ".join(sorted({rows[j] for j in want})))
PY
)
  # shellcheck disable=SC2086
  python3 jet-closure.py $roots > "$work/scope.txt"
  export JET_ONLY_MODULES="$work/scope.txt"
  JET_TARGETS=$(for r in $roots; do printf '%s.vo ' "${r//.//}"; done)
  export JET_TARGETS
  echo "== scope: $(echo "$jets" | tr ',' ' ' | wc -w | tr -d ' ') jet(s), $(wc -l < "$work/scope.txt" | tr -d ' ') module(s)"
fi
for m in $(awk '!/^#/ && NF==2 {print $1}' C/jet_public_theorems.txt | sort -u); do
  f=${m//./\/}.v
  grep -qx "$f" _CoqProject.jets || { echo "$f not in _CoqProject.jets" >&2; exit 1; }
done

if $build; then
  echo "== build (make -j$jobs)"
  bash build-jets.sh -j"$jobs"
fi

echo "== coqchk"
# Every built jet module is kernel-checked, not only those with public theorems.
mods=$(grep -E '^C/.*\.v$' _CoqProject.jets | sed 's/\.v$//; s|/|.|g' | sort -u)
if [[ -n "$jets" ]]; then mods=$(comm -12 <(echo "$mods") <(sort "$work/scope.txt")); fi
mods=$(echo "$mods" | tr '\n' ' ')
# shellcheck disable=SC2086
if ! bash build-jets.sh --coqchk -silent -o $mods > "$work/coqchk.out" 2>&1; then
  cat "$work/coqchk.out" >&2
  exit 1
fi
axioms=$(awk '/^\* Axioms:/{f=1;next} f&&NF==0{exit} f{print $1}' "$work/coqchk.out" | sort)
grep -q 'Constants/Inductives relying on type-in-type: <none>' "$work/coqchk.out"
grep -q 'unsafe (co)fixpoints: <none>' "$work/coqchk.out"
grep -q 'positivity is assumed: <none>' "$work/coqchk.out"
if [[ -n "$jets" ]]; then
  # A scoped run sees a subset of the library axioms; it never rewrites the list.
  extra=$(comm -23 <(printf '%s\n' "$axioms") C/jet_coqchk_axioms.expected)
  if [[ -n "$extra" ]]; then
    echo "coqchk axioms outside C/jet_coqchk_axioms.expected: $extra" >&2; exit 1
  fi
elif $update; then printf '%s\n' "$axioms" > C/jet_coqchk_axioms.expected
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
  COMPCERT=${COMPCERT:-$JET_DEPS/compcert-3.14} JET_SYSROOT=$JET_SYSROOT \
    bash C/check-elements-jets-generation.sh
fi
inputs_after=$(audit_inputs)
if [[ "$inputs_before" != "$inputs_after" ]]; then
  echo 'audit inputs changed during verification; rerun against the final sources' >&2
  exit 1
fi
echo "audit input SHA-256: $inputs_after"
if [[ -n "$jets" ]]; then scoped=" for jets: $jets"; else scoped=""; fi
if $update; then
  echo "candidate snapshots generated$scoped; review their diffs, then rerun --accept without update flags"
elif $accept && [[ -n "$jets" ]]; then
  echo "scoped jet acceptance passed$scoped (build, kernel, reviewed snapshots, negative tests, five ASTs)"
elif $accept; then
  echo 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
elif ! $build; then
  echo 'jet artifact checks passed (--no-build; current sources were not rebuilt by this run)'
elif ! $ast; then
  echo 'jet proof checks passed (AST regeneration not run; use --accept for acceptance)'
else
  echo 'all jet checks passed'
fi
