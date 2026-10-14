#!/usr/bin/env python3
"""Source gate for C/jet_elements_prim.v against the canonical Haskell
Simplicity/Elements/Primitive.hs: the primitive constructors, their order,
their source and target types, and their names must correspond exactly.
It does not check the semantics clauses; those need human review.
Usage: check-elements-prim-port.py REPO_ROOT"""
import re, sys

root = sys.argv[1]
hs = open(root + "/Haskell/Elements/Simplicity/Elements/Primitive.hs").read()
coq = open(root + "/Coq/C/jet_elements_prim.v").read()

def parse_hs_type(s):
    """Tokenize and parse a Haskell type into a nested tuple."""
    toks = re.findall(r"\(\)|[(),]|[A-Za-z0-9]+", s)
    pos = 0
    def atom():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "()":
            return ("Unit",)
        if t == "(":
            first = app()
            if toks[pos] == ",":
                pos += 1
                second = app()
                assert toks[pos] == ")"; pos += 1
                return ("Prod", first, second)
            assert toks[pos] == ")"; pos += 1
            return first
        return (t,)
    def app():
        nonlocal pos
        head = atom()
        args = []
        while pos < len(toks) and toks[pos] not in (")", ","):
            args.append(atom())
        if not args:
            return head
        name = head[0]
        if name == "Either":
            return ("Sum", args[0], args[1])
        return (name,) + tuple(args)
    r = app()
    assert pos == len(toks), (s, toks[pos:])
    return r

def parse_coq_type(s):
    toks = re.findall(r"[()]|[A-Za-z0-9]+", s)
    pos = 0
    def atom():
        nonlocal pos
        t = toks[pos]; pos += 1
        if t == "(":
            r = app()
            assert toks[pos] == ")"; pos += 1
            return r
        return (t,)
    def app():
        nonlocal pos
        head = atom()
        args = []
        while pos < len(toks) and toks[pos] != ")":
            args.append(atom())
        return head if not args else (head[0],) + tuple(args)
    r = app()
    assert pos == len(toks), (s, toks[pos:])
    return r

def norm(t):
    """PubKey is Word256 in both sources' encodings."""
    if t == ("PubKey",):
        return ("Word256",)
    return (t[0],) + tuple(norm(x) for x in t[1:])

def split_two(s, parse):
    """Split 'T1 T2' into two top-level type atoms."""
    depth, parts, cur = 0, [], ""
    for tok in re.findall(r"\(\)|[()]|[^\s()]+|\s+", s.strip()):
        if tok.isspace() and depth == 0:
            if cur:
                parts.append(cur); cur = ""
            continue
        if tok == "(":
            depth += 1
        elif tok == ")":
            depth -= 1
        cur += tok if not tok.isspace() else " "
    if cur:
        parts.append(cur)
    assert len(parts) == 2, (s, parts)
    return tuple(norm(parse(p)) for p in parts)

hs_prims = [(m.group(1), split_two(m.group(2), parse_hs_type))
            for m in re.finditer(r"^  (\w+) :: Prim (.+)$", hs, re.M)]
block = coq[coq.index("Inductive prim : Ty -> Ty -> Set :="):coq.index("Definition t := prim.")]
block = re.sub(r"\s+", " ", block)
coq_prims = [(m.group(1), split_two(m.group(2), parse_coq_type))
             for m in re.finditer(r"\| (\w+) : prim (.+?)(?= \||\.\s*$)", block)]
hs_names = dict(re.findall(r'^primName (\w+) = "(\w+)"', hs, re.M))
coq_names = dict(re.findall(r'^\| (\w+) => "(\w+)"', coq, re.M))
prefix_hs = re.search(r'^primPrefix = "(\w+)"', hs, re.M).group(1)
prefix_coq = re.search(r'Definition primName : string := "(\w+)"', coq).group(1)

errors = []
if len(hs_prims) != 31:
    errors.append("expected 31 Haskell primitives, found %d" % len(hs_prims))
if [n for n, _ in hs_prims] != [n for n, _ in coq_prims]:
    errors.append("constructor lists differ: %s vs %s" %
                  ([n for n, _ in hs_prims], [n for n, _ in coq_prims]))
for (hn, ht), (cn, ct) in zip(hs_prims, coq_prims):
    if hn == cn and ht != ct:
        errors.append("%s: types differ: Haskell %s, Coq %s" % (hn, ht, ct))
if hs_names != coq_names:
    errors.append("primName tables differ")
if prefix_hs != prefix_coq:
    errors.append("prefix differs")
if errors:
    sys.exit("\n".join(errors))
print("Elements primitive signature matches Haskell: %d constructors, types, names and prefix" % len(hs_prims))
