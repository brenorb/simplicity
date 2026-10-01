#!/usr/bin/env bash
# Assumption gate for the public jet theorems.
#
# Runs `Print Assumptions` for every theorem listed in C/jet_public_theorems.txt
# and compares the axiom set of each theorem with C/jet_assumptions.expected.
# The script fails when
#   * an axiom outside the inherited allowlist below appears anywhere,
#   * a theorem depends on an axiom set different from the recorded one
#     (including an inherited axiom that it did not depend on before), or
#   * a listed theorem is missing.
# `Print Assumptions` output is therefore an input to the gate, not the gate.
# After an intentional change, review the diff and run with --update.
#
# Requires a built project (Coq/build-jets.sh).
set -euo pipefail
cd "$(dirname "$0")"

update=false
[[ "${1:-}" == "--update" ]] && update=true

list=C/jet_public_theorems.txt
expected=C/jet_assumptions.expected
work=$(mktemp -d "${TMPDIR:-/tmp}/jet-audit.XXXXXX")
trap 'rm -rf "$work"' EXIT

{
  echo "Set Warnings \"-notation-overridden\"."
  awk '!/^#/ && NF==2 {print $1}' "$list" | sort -u | sed 's/^/Require Import /; s/$/./'
  # Locate wraps long qualified names onto a second line. Explicit, single
  # string markers keep theorem boundaries independent of pretty-print width;
  # Print Assumptions still fails compilation if the named theorem is absent.
  awk '!/^#/ && NF==2 {printf "Goal True. idtac \"JET_ASSUMPTIONS %s.%s\". exact I. Qed.\nPrint Assumptions %s.%s.\n", $1, $2, $1, $2}' "$list"
} > "$work/audit.v"

bash build-jets.sh --coqc -q "$work/audit.v" > "$work/audit.out"

python3 - "$work/audit.out" "$expected" "$update" <<'PY'
import re, sys
out, expected, update = sys.argv[1], sys.argv[2], sys.argv[3] == "true"
INHERITED = {
    # Coq standard library
    "Classical_Prop.classic",
    "FunctionalExtensionality.functional_extensionality_dep",
    "ClassicalDedekindReals.sig_forall_dec",
    "ClassicalDedekindReals.sig_not_dec",
    # CompCert: parameterized external-call and inline-assembly semantics
    "Events.external_functions_sem",
    "Events.external_functions_properties",
    "Events.inline_assembly_sem",
    "Events.inline_assembly_properties",
}
result, cur, axioms = {}, None, None
for line in open(out):
    line = line.rstrip("\n")
    m = re.match(r"^JET_ASSUMPTIONS (\S+)$", line)
    if m:
        cur = m.group(1); result[cur] = set(); axioms = False; continue
    if line.startswith("Axioms:"):
        axioms = True; continue
    if line.startswith("Closed under the global context"):
        axioms = False; continue
    if axioms and cur and line and not line[0].isspace():
        result[cur].add(line.split()[0])
text = "".join("%s : %s\n" % (t, ", ".join(sorted(a)) if a else "closed")
               for t, a in sorted(result.items()))
bad = sorted({a for s in result.values() for a in s} - INHERITED)
if bad:
    print("Unexpected axioms (not inherited from Coq/CompCert):", *bad, sep="\n  ")
    sys.exit(1)
listed = [l.split() for l in open("C/jet_public_theorems.txt") if l.strip() and not l.startswith("#")]
missing = [f"{m}.{t}" for m, t in listed if f"{m}.{t}" not in result]
if missing:
    sys.exit("missing from audit output: %s" % missing)
if update:
    open(expected, "w").write(text); print("updated", expected); sys.exit(0)
want = open(expected).read()
if text != want:
    import difflib
    sys.stdout.writelines(difflib.unified_diff(want.splitlines(True), text.splitlines(True),
                                               expected, "current"))
    sys.exit("assumption sets differ from %s" % expected)
print("assumption audit passed: %d theorems, %d closed" % (len(result), sum(1 for a in result.values() if not a)))
PY
