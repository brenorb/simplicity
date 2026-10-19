#!/usr/bin/env bash
# Scoped acceptance of the fe_multiply/fe_square registration while the
# repository-wide check-jets.sh --accept is blocked by the baseline (see
# ACCEPTANCE-STATUS.md). Run from a tree whose Coq project has been built with
# build-jets.sh (-k); records every step's exit status in OUT/STATUS.
#
#   bash proof-work/fe-multiply-parallel/scoped-acceptance.sh OUT
#
# Steps:
#   1. original-target guard and every static check of check-jets.sh;
#   2. build status of every _CoqProject.jets module (from the .vo files present);
#   3. recursive coqchk of the two registered public modules (whole closure),
#      library axioms compared with C/jet_coqchk_axioms.expected;
#   4. exact assumption records (same printer and allowlist as
#      audit-jet-assumptions.sh) for every newly listed public theorem, and the
#      candidate C/jet_assumptions.expected (existing records + new ones);
#   5. candidate contract records (Check/Print exactly as audit-jet-contracts.sh)
#      for the new entries, printed with every built public module imported.
# Reviewed snapshots are never modified.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(git -C "$HERE" rev-parse --show-toplevel)
OUT=${1:?usage: scoped-acceptance.sh OUT}
mkdir -p "$OUT"; OUT=$(cd "$OUT" && pwd)
cd "$REPO/Coq"
ulimit -s 65520 2>/dev/null || true
st() { echo "$1 $2" >> "$OUT/STATUS"; }
echo "revision $(git rev-parse HEAD) dirty=$(git status --porcelain -- . ../C ../Haskell | grep -v '^??' | wc -l | tr -d ' ')" > "$OUT/STATUS"
git diff --quiet 91d89bac HEAD -- ../C ../Haskell Simplicity ':(exclude)../C/test.c'; st guard $?

for c in check-jet-source-target.py test-jet-source-target.py scan-jet-proofs.py jet-coverage.py \
    test-jet-coverage.py check-fullshift-specification.py test-fullshift-specification.py \
    check-secp-normalize-specification.py test-secp-normalize-specification.py \
    check-secp-predicates-specification.py test-secp-predicates-specification.py \
    check-bitcoin-primitive-identity.py test-bitcoin-primitive-identity.py test-jet-audit-inputs.py; do
  python3 "$c" > "$OUT/static-$c.log" 2>&1; st "static:$c" $?
done
for g in check test; do
  python3 "mul-review/$g-mul-wiring.py" --repo .. --candidates C --dependencies C > "$OUT/static-$g-mul-wiring.log" 2>&1
  st "static:mul-review/$g-mul-wiring.py" $?
done
python3 jet-coverage.py > "$OUT/coverage.txt" 2>&1; st coverage-count $?

missing=0; : > "$OUT/unbuilt-modules.txt"
for f in $(grep '^C/.*\.v$' _CoqProject.jets); do
  if [ ! -f "${f%.v}.vo" ] || [ "${f%.v}.vo" -ot "$f" ]; then echo "$f" >> "$OUT/unbuilt-modules.txt"; missing=$((missing+1)); fi
done
st "unbuilt-jet-modules:$missing" 0

( time bash build-jets.sh --coqchk -silent -o C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local ) > "$OUT/coqchk.log" 2>&1; rc=$?
st coqchk $rc
awk '/^\* Axioms:/{f=1;next} f&&NF==0{exit} f{print $1}' "$OUT/coqchk.log" | sort > "$OUT/coqchk-axioms.txt"
diff "$OUT/coqchk-axioms.txt" C/jet_coqchk_axioms.expected > /dev/null; st coqchk-axioms-match $?
for k in 'type-in-type: <none>' 'unsafe (co)fixpoints: <none>' 'positivity is assumed: <none>'; do
  grep -q "$k" "$OUT/coqchk.log"; st "coqchk:${k%%:*}" $?
done

new=$(sed -n '/^# Original field multiplication and squaring\./,$p' C/jet_public_theorems.txt | awk '!/^#/ && NF==2')
newdefs=$(sed -n '/^# Original field multiplication and squaring\./,$p' C/jet_contract_definitions.txt | awk '!/^#/ && NF==2')
{
  echo 'Set Warnings "-notation-overridden".'
  echo "$new" | awk '{print $1}' | sort -u | sed 's/^/Require Import /; s/$/./'
  echo "$new" | awk '{printf "Goal True. idtac \"JET_ASSUMPTIONS %s.%s\". exact I. Qed.\nPrint Assumptions %s.%s.\n", $1, $2, $1, $2}'
} > "$OUT/audit-new.v"
bash build-jets.sh --coqc -q "$OUT/audit-new.v" > "$OUT/audit-new.out" 2>&1; st assumptions-print $?
python3 - "$OUT/audit-new.out" C/jet_assumptions.expected "$OUT" <<'PY'
import re, sys
out, expected, d = sys.argv[1:]
INHERITED = {"Classical_Prop.classic", "FunctionalExtensionality.functional_extensionality_dep",
    "ClassicalDedekindReals.sig_forall_dec", "ClassicalDedekindReals.sig_not_dec",
    "Events.external_functions_sem", "Events.external_functions_properties",
    "Events.inline_assembly_sem", "Events.inline_assembly_properties"}
result, cur, axioms = {}, None, None
for line in open(out):
    line = line.rstrip("\n")
    m = re.match(r"^JET_ASSUMPTIONS (\S+)$", line)
    if m: cur = m.group(1); result[cur] = set(); axioms = False; continue
    if line.startswith("Axioms:"): axioms = True; continue
    if line.startswith("Closed under the global context"): axioms = False; continue
    if axioms and cur and line and not line[0].isspace(): result[cur].add(line.split()[0])
bad = sorted({a for s in result.values() for a in s} - INHERITED)
old = {l.split(" : ")[0]: l for l in open(expected) if l.strip()}
clash = [t for t in result if t in old]
new = {t: "%s : %s\n" % (t, ", ".join(sorted(a)) if a else "closed") for t, a in result.items()}
open(d + "/assumptions-new.txt", "w").writelines(new[t] for t in sorted(new))
merged = dict(old); merged.update(new)
open(d + "/jet_assumptions.expected.candidate", "w").writelines(merged[t] for t in sorted(merged))
print("new theorems", len(new), "closed", sum(1 for a in result.values() if not a),
      "unexpected axioms", bad, "already recorded", clash)
sys.exit(1 if bad or clash else 0)
PY
st assumptions-allowlist-and-additions-only $?
diff -u C/jet_assumptions.expected "$OUT/jet_assumptions.expected.candidate" > "$OUT/jet_assumptions.diff"
grep -c '^-[^-]' "$OUT/jet_assumptions.diff" > "$OUT/assumptions-removed-lines.txt"

{
  echo 'Set Warnings "-notation-overridden".'
  cat C/jet_public_theorems.txt C/jet_contract_definitions.txt | awk '!/^#/ && NF==2 {print $1}' | sort -u |
    while read -r m; do f=${m//./\/}.vo; [ -f "$f" ] && echo "$m"; done |
    awk '/^Simplicity\./ {print "Require " $0 "."; next} {print "Require Import " $0 "."}'
  echo 'Import Simplicity.BitMachine Simplicity.Translate.'
  echo 'Set Printing All.'
  echo 'Set Printing Width 120.'
  echo "$new" | awk '{printf "Check %s.%s.\n", $1, $2}'
  echo "$newdefs" | awk '{printf "Print %s.%s.\n", $1, $2}'
} > "$OUT/contracts-new.v"
bash build-jets.sh --coqc -q "$OUT/contracts-new.v" 2>&1 | sed 's/[[:blank:]]*$//' > "$OUT/contracts-new.out"; st contracts-print ${PIPESTATUS[0]}
exit 0
