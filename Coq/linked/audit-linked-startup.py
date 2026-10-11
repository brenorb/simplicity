#!/usr/bin/env python3
"""Check the assumption reports of the linked startup theorems: each must be
within the eight assumptions inherited by the accepted SHA-unit proofs."""
import re, sys

INHERITED = {
    "ClassicalDedekindReals.sig_forall_dec", "ClassicalDedekindReals.sig_not_dec",
    "Classical_Prop.classic", "Events.external_functions_sem",
    "Events.inline_assembly_sem", "FunctionalExtensionality.functional_extensionality_dep",
    "Events.external_functions_properties", "Events.inline_assembly_properties",
}
blocks = re.split(r"^@@ ", open(sys.argv[1]).read(), flags=re.M)[1:]
expected = int(sys.argv[2]) + 1
if len(blocks) != expected:
    sys.exit("expected %d reports, found %d" % (expected, len(blocks)))
for block in blocks:
    head, _, body = block.partition("\n")
    found = set()
    if not body.startswith("Closed under the global context"):
        found = set(re.findall(r"^([A-Za-z_][\w.]*) :", body, re.M)) | \
                set(re.findall(r"^([A-Za-z_][\w.]*)$", body, re.M))
        found.discard("Axioms")
    if not found <= INHERITED:
        sys.exit("%s: unexpected assumptions %s" % (head.strip(), sorted(found - INHERITED)))
print("assumption audit passed: %d linked startup contracts and the initialization theorem" % (expected - 1))
