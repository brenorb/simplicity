#!/usr/bin/env python3
"""The SHA proof modules used for the Elements environment builders mention
C definitions of the SHA unit; each must exist in the Elements environment
unit (C/jets_elements_env.v) with exactly the same generated text.  The
frame-hash helpers readHash/writeHash live in elements/elementsJets.c, which
is not part of that unit; the one module that mentions them
(jet_sha_hash_io) is not used here.  Also the Elements tap operations must be
the ones of the Elements jets unit.  Run from Coq/."""
import glob, re, sys

def defs(path):
    text = open(path).read()
    return {m.group(1): m.group(2)
            for m in re.finditer(r"^Definition (f_\w+|v_\w+) := (.*?)\n\|\}\.\n", text, re.S | re.M)}

sha, env, elements = defs("C/jets_sha.v"), defs("C/jets_elements_env.v"), defs("C/jets_elements.v")
used = set()
for path in glob.glob("C/jet_sha*.v"):
    if path.endswith("jet_sha_hash_io.v"):
        continue
    used |= set(re.findall(r"\b((?:f|v)_[A-Za-z0-9_]+)\b", open(path).read())) & set(sha)
bad = sorted(name for name in used if env.get(name) != sha[name])
for name in ("f_simplicity_make_tapleaf", "v_tagName__1", "f_simplicity_make_tapbranch", "v_tagName__2"):
    if env.get(name) != elements[name]:
        bad.append(name + " (differs from the Elements jets unit)")
if bad:
    sys.exit("definitions that differ in the Elements environment unit: " + ", ".join(bad))
print("%d SHA-unit definitions and the Elements tap operations are identical in the Elements environment unit" % len(used))
