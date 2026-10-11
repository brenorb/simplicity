#!/usr/bin/env python3
"""Assumption audit of the startup-invariant theorems (run by build-startup.sh --check).

`gen DIR OUT` writes a Coq file printing the assumptions of every theorem and
lemma of the startup modules; `check DIR LOG` requires each set to be within
the eight assumptions already inherited by the accepted SHA-unit proofs.
"""
import glob, os, re, sys

INHERITED = {
    "ClassicalDedekindReals.sig_forall_dec", "ClassicalDedekindReals.sig_not_dec",
    "Classical_Prop.classic", "Events.external_functions_sem",
    "Events.inline_assembly_sem", "FunctionalExtensionality.functional_extensionality_dep",
    "Events.external_functions_properties", "Events.inline_assembly_properties",
}

def items(directory):
    out = []
    for path in sorted(glob.glob(os.path.join(directory, "*.v"))):
        mod = os.path.basename(path)[:-2]
        for name in re.findall(r"^(?:Theorem|Lemma) (\w+)", open(path).read(), re.M):
            out.append((mod, name))
    return out

mode, directory, target = sys.argv[1:4]
found_items = items(directory)
if mode == "gen":
    with open(target, "w") as f:
        for mod, name in found_items:
            f.write("Require JetStartup.%s.\n" % mod)
            f.write('Goal True. idtac "@@ %s.%s". Abort.\n' % (mod, name))
            f.write("Print Assumptions JetStartup.%s.%s.\n" % (mod, name))
else:
    blocks = re.split(r"^@@ ", open(target).read(), flags=re.M)[1:]
    if len(blocks) != len(found_items):
        sys.exit("expected %d reports, found %d" % (len(found_items), len(blocks)))
    specs = 0
    for (mod, name), block in zip(found_items, blocks):
        head, _, body = block.partition("\n")
        if head.strip() != "%s.%s" % (mod, name):
            sys.exit("report order mismatch at %s" % head)
        found = set()
        if not body.startswith("Closed under the global context"):
            found = set(re.findall(r"^([A-Za-z_][\w.]*) :", body, re.M)) | \
                    set(re.findall(r"^([A-Za-z_][\w.]*)$", body, re.M))
            found.discard("Axioms")
        if not found <= INHERITED:
            sys.exit("%s.%s: unexpected assumptions %s" % (mod, name, sorted(found - INHERITED)))
        specs += name.endswith("_startup_spec")
    print("assumption audit passed: %d results, %d jet contracts over the invariant" %
          (len(found_items), specs))
