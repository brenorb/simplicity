#!/usr/bin/env python3
"""Assumption audit of the linked theorems (run by audit-linked.sh).

Mode `gen DIR OUT`: write a Coq file printing the assumptions of every
`_linked` theorem, of `memcpy_model_holds` and of the linking theorems.
Mode `check DIR LOG`: every `_linked` theorem and `memcpy_model_holds` must
depend on exactly the six assumptions inherited by the accepted proofs;
`linked_ast_is_compcert_link` must be closed; the Clight-level linking
theorem may depend only on CompCert's `Axioms.proof_irr`.
"""
import glob, os, re, sys

INHERITED = {
    "ClassicalDedekindReals.sig_forall_dec", "ClassicalDedekindReals.sig_not_dec",
    "Classical_Prop.classic", "Events.external_functions_sem",
    "Events.inline_assembly_sem", "FunctionalExtensionality.functional_extensionality_dep",
}
EXTRA = [("jet_memcpy_model", "memcpy_model_holds", INHERITED),
         ("jet_linked_program", "linked_ast_is_compcert_link", set()),
         ("jet_linked_program", "linked_program_is_compcert_link", {"Axioms.proof_irr"})]

def theorems(directory):
    out = []
    for path in sorted(glob.glob(os.path.join(directory, "*.v"))):
        mod = os.path.basename(path)[:-2]
        for name in re.findall(r"^Theorem (\w+_linked) :", open(path).read(), re.M):
            out.append((mod, name, INHERITED))
    return out + EXTRA

mode, directory, target = sys.argv[1:4]
items = theorems(directory)
if mode == "gen":
    with open(target, "w") as f:
        for mod, name, _ in items:
            f.write("Require C.%s.\n" % mod)
            f.write('Goal True. idtac "@@ %s.%s". Abort.\n' % (mod, name))
            f.write("Print Assumptions C.%s.%s.\n" % (mod, name))
else:
    log = open(target).read()
    blocks = re.split(r"^@@ ", log, flags=re.M)[1:]
    if len(blocks) != len(items):
        sys.exit("expected %d reports, found %d" % (len(items), len(blocks)))
    for (mod, name, allowed), block in zip(items, blocks):
        head, _, body = block.partition("\n")
        if head.strip() != "%s.%s" % (mod, name):
            sys.exit("report order mismatch at %s" % head)
        if body.startswith("Closed under the global context"):
            found = set()
        else:
            found = set(re.findall(r"^([A-Za-z_][\w.]*) :", body, re.M)) | \
                    set(re.findall(r"^([A-Za-z_][\w.]*)$", body, re.M))
            found.discard("Axioms")
            # the printed qualification depends on which libraries are loaded
            found = {"Axioms.proof_irr" if n.endswith(".Axioms.proof_irr") else n for n in found}
        if found != allowed:
            sys.exit("%s.%s: assumptions %s, expected %s" % (mod, name, sorted(found), sorted(allowed)))
    print("assumption audit passed: %d theorems (%d linked jet contracts)" %
          (len(items), len(items) - len(EXTRA)))
