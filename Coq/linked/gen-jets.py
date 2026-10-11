#!/usr/bin/env python3
"""Derive the linked core jets program from the accepted generated AST.

The only changes to Coq/C/jets.v are: the identifier used by the concrete
memcpy parameter is declared if missing, the function definition generated
from jet_memcpy_exact.c is inserted, and the external declaration of memcpy
is replaced, at the same position of the global definition list, by that
internal definition.  Every edit is checked to apply exactly once.
"""
import re, sys

jets_path, impl_path, out_path = sys.argv[1:4]
jets = open(jets_path).read()
impl = open(impl_path).read()

m = re.search(r"^Definition f_memcpy := \{\|.*?^\|\}\.\n", impl, re.S | re.M)
if not m:
    sys.exit("f_memcpy not found in implementation AST")
f_memcpy = m.group(0)

# every identifier used by the implementation must denote the same name
for ident in sorted(set(re.findall(r"\b_[A-Za-z0-9_']+\b", f_memcpy))):
    d = re.search(r"^Definition %s : ident := (.*)\.$" % re.escape(ident), impl, re.M)
    if not d:
        sys.exit("identifier %s undeclared in implementation AST" % ident)
    line = d.group(0) + "\n"
    j = re.search(r"^Definition %s : ident := (.*)\.$" % re.escape(ident), jets, re.M)
    if j is None:
        anchor = "Definition _memcpy : ident := $\"memcpy\".\n"
        if jets.count(anchor) != 1:
            sys.exit("identifier anchor not unique")
        jets = jets.replace(anchor, anchor + line)
    elif j.group(1) != d.group(1):
        sys.exit("identifier %s differs between the programs" % ident)

external = ''' (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
     (tptr tvoid) cc_default)) ::
'''
if jets.count(external) != 1:
    sys.exit("external memcpy declaration not found exactly once")
jets = jets.replace(external, " (_memcpy, Gfun(Internal f_memcpy)) ::\n")

anchor = "Definition composites : list composite_definition :=\n"
if jets.count(anchor) != 1 or "Definition f_memcpy" in jets:
    sys.exit("composites anchor not unique or f_memcpy already present")
jets = jets.replace(anchor, f_memcpy + "\n" + anchor)
open(out_path, "w").write(jets)
