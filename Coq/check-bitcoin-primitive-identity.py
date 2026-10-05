#!/usr/bin/env python3
"""Compare the extended Coq primitive interface with the canonical Haskell source.

This checks constructor types, names and the commitment-tag namespace. It does
not prove the Haskell hashing functions or the environment projection correct.
Coq separately checks the tag and CurrentIndex compatibility lemmas.
"""
import importlib.util
import os
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
MODEL = COQ / "C/jet_bitcoin_ext_prim.v"
BASE_MODEL = COQ / "Simplicity/Primitive/Bitcoin.v"
CANONICAL = REPO / "Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs"
scanner_spec = importlib.util.spec_from_file_location("jet_scanner", COQ / "scan-jet-proofs.py")
scanner = importlib.util.module_from_spec(scanner_spec)
scanner_spec.loader.exec_module(scanner)


def check(model=MODEL, canonical=CANONICAL, base_model=BASE_MODEL):
    raw = model.read_text()
    code = scanner.code_only(raw)
    haskell = re.sub(r"--[^\n]*", "", canonical.read_text())
    # Locate the string in the original source, but only at a declaration that
    # the comment/string-aware scanner identifies as code.
    prefix_decl = re.search(r"\bDefinition primName\s*:\s*string\s*:=", code)
    canonical_prefix = re.search(r'^primPrefix\s*=\s*"([^"]+)"', haskell, re.M)
    prefix = re.match(r'\s*"([^"]+)"\s*\.', raw[prefix_decl.end():]) if prefix_decl else None
    if not prefix or not canonical_prefix or prefix[1] != canonical_prefix[1]:
        raise ValueError("Bitcoin primitive tag namespace differs from canonical Haskell")
    constructors = re.findall(r"\|\s*(\w+)\s*:\s*prim\s+([^\n.]+)", code)
    if not constructors:
        raise ValueError("no extended Bitcoin constructors found")
    canonical_types = dict(re.findall(r"^\s*([A-Z]\w*)\s*::\s*Prim\s+(.+)$", haskell, re.M))
    names = dict(re.findall(r'^primName\s+(\w+)\s*=\s*"([^"]+)"', haskell, re.M))
    coq_names = {}
    for match in re.finditer(r"\|\s*(\w+)\s*=>", code):
        value = re.match(r'\s*"([^"]+)"', raw[match.end():])
        if value:
            coq_names[match[1]] = value[1]
    def normalize(value):
        value = value.replace("()", "Unit").replace("PubKey", "Word256")
        value = re.sub(r"\(([^(),]+),([^(),]+)\)", r"(Prod \1 \2)", value)
        value = re.sub(r"\bS\b", "Sum Unit", value)
        return re.sub(r"[\s()]", "", value)
    for constructor, signature in constructors:
        if constructor not in canonical_types or normalize(signature) != normalize(canonical_types[constructor]):
            raise ValueError(f"Bitcoin primitive type mismatch: {constructor}")
        if coq_names.get(constructor) != names.get(constructor):
            raise ValueError(f"Bitcoin primitive name mismatch: {constructor}")
    # The older base signature also contains compatibility-only constructors
    # for composed programs. They are auxiliary, not canonical primitives.
    legacy = {"InputsHash", "OutputsHash", "NumInputs", "TotalInputValue",
              "CurrentPrevOutpoint", "CurrentValue", "CurrentSequence",
              "NumOutputs", "TotalOutputValue"}
    base_raw = base_model.read_text()
    base_code = scanner.code_only(base_raw)
    base_prefix_decl = re.search(r"\bDefinition primName\s*:\s*string\s*:=", base_code)
    base_prefix = re.match(r'\s*"([^"]+)"\s*\.', base_raw[base_prefix_decl.end():]) if base_prefix_decl else None
    if not base_prefix or base_prefix[1] != canonical_prefix[1]:
        raise ValueError("Bitcoin base primitive tag namespace differs from canonical Haskell")
    base_constructors = re.findall(r"\|\s*(\w+)\s*:\s*prim\s+([^\n.]+)", base_code)
    if not base_constructors:
        raise ValueError("no base Bitcoin constructors found")
    base_names = {}
    for match in re.finditer(r"\|\s*(\w+)\s*=>", base_code):
        value = re.match(r'\s*"([^"]+)"', base_raw[match.end():])
        if value:
            base_names[match[1]] = value[1]
    for constructor, signature in base_constructors:
        if constructor in legacy:
            continue
        if constructor not in canonical_types or normalize(signature) != normalize(canonical_types[constructor]):
            raise ValueError(f"Bitcoin base primitive type mismatch: {constructor}")
        if base_names.get(constructor) != names.get(constructor):
            raise ValueError(f"Bitcoin base primitive name mismatch: {constructor}")
    covered = {c for c, _ in constructors} | {c for c, _ in base_constructors if c not in legacy}
    if covered != set(canonical_types):
        raise ValueError("Bitcoin canonical primitive constructor coverage differs")
    return len(constructors)


if __name__ == "__main__":
    try:
        count = check()
    except (OSError, ValueError) as error:
        sys.exit(str(error))
    print(f"Bitcoin primitive identities match canonical Haskell: {count} constructors")
