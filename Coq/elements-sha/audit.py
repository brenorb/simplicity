#!/usr/bin/env python3
"""Check the assumption reports of the Elements-SHA theorems.  Each report
must be within the six assumptions inherited by the accepted jet proofs;
reports marked "forward" (start-up invariant preservation, which uses that
Clight execution never frees or re-permissions existing blocks) may also use
CompCert's two properties of the external-call semantics, as the SHA unit's
start-up tree does.

Usage: audit.py LOG EXPECTED_REPORTS"""
import re, sys

INHERITED = {
    "ClassicalDedekindReals.sig_forall_dec", "ClassicalDedekindReals.sig_not_dec",
    "Classical_Prop.classic", "Events.external_functions_sem",
    "Events.inline_assembly_sem", "FunctionalExtensionality.functional_extensionality_dep",
}
FORWARD = INHERITED | {"Events.external_functions_properties", "Events.inline_assembly_properties"}
blocks = re.split(r"^@@ ", open(sys.argv[1]).read(), flags=re.M)[1:]
expected = int(sys.argv[2])
if len(blocks) != expected:
    sys.exit("expected %d reports, found %d" % (expected, len(blocks)))
forward = 0
for block in blocks:
    head, _, body = block.partition("\n")
    allowed = FORWARD if head.strip().endswith(" forward") else INHERITED
    forward += allowed is FORWARD
    found = set()
    if not body.startswith("Closed under the global context"):
        if not body.startswith("Axioms:"):
            sys.exit("%s: no assumption report" % head.strip())
        found = set(re.findall(r"^([A-Za-z_][\w.]*) :", body, re.M)) | \
                set(re.findall(r"^([A-Za-z_][\w.]*)$", body, re.M))
        found.discard("Axioms")
    if not found <= allowed:
        sys.exit("%s: unexpected assumptions %s" % (head.strip(), sorted(found - allowed)))
print("assumption audit passed: %d reports (%d within the six inherited assumptions, %d start-up reports within eight)"
      % (expected, expected - forward, forward))
