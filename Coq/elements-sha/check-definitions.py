#!/usr/bin/env python3
"""Every C definition (function or global variable) of the SHA unit that a
C/jet_sha*.v proof module mentions must exist in the Elements unit with
exactly the same generated text.  Run from Coq/."""
import glob, re, sys

def defs(path):
    text = open(path).read()
    return {m.group(1): m.group(2)
            for m in re.finditer(r"^Definition (f_\w+|v_\w+) := (.*?)\n\|\}\.\n", text, re.S | re.M)}

sha, elements = defs("C/jets_sha.v"), defs("C/jets_elements.v")
used = set()
for path in glob.glob("C/jet_sha*.v"):
    used |= set(re.findall(r"\b((?:f|v)_[A-Za-z0-9_]+)\b", open(path).read())) & set(sha)
bad = sorted(name for name in used if elements.get(name) != sha[name])
if bad:
    sys.exit("SHA proof modules mention definitions that differ in the Elements unit: " + ", ".join(bad))
print("%d definitions used by the SHA proof modules are identical in the Elements unit" % len(used))
