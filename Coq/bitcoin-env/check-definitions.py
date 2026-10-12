#!/usr/bin/env python3
"""Every C function and global variable of the SHA unit must exist in the
environment unit (the SHA unit followed by bitcoin/env.c) with exactly the
same generated text; the composite definitions of the SHA unit must be a
prefix of the environment unit's (which adds the raw input structures).
Run from Coq/."""
import re, sys

def defs(path):
    text = open(path).read()
    d = {m.group(1): m.group(2)
         for m in re.finditer(r"^Definition (f_\w+|v_\w+) := (.*?)\n\|\}\.\n", text, re.S | re.M)}
    m = re.search(r"^Definition composites : list composite_definition :=\n\((.*?) nil\)\.\n\nDefinition global_definitions", text, re.S | re.M)
    return d, m.group(1)

(sha, sha_comp), (env, env_comp) = defs("C/jets_sha.v"), defs("C/jets_bitcoin_env.v")
bad = sorted(name for name in sha if env.get(name) != sha[name])
if not env_comp.startswith(sha_comp):
    bad.append("composites (not a prefix)")
if bad:
    sys.exit("definitions of the SHA unit that differ in the environment unit: " + ", ".join(bad))
new = sorted(set(env) - set(sha))
print("%d definitions of the SHA unit are identical in the environment unit; new: %s" % (len(sha), ", ".join(new)))
