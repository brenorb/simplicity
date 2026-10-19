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
# Mismatches between the frozen base model and Haskell are reported, never
# corrected. Each one must be documented in this report by a marker line
#   <!-- gate bitcoin-base KIND CONSTRUCTOR "COQ" "HASKELL" -->
MISMATCH_REPORT = COQ / "C/JET_BITCOIN_MODEL_MISMATCHES.md"
# Constructors of the older base signature used only by composed programs.
LEGACY = {"InputsHash", "OutputsHash", "NumInputs", "TotalInputValue",
          "CurrentPrevOutpoint", "CurrentValue", "CurrentSequence",
          "NumOutputs", "TotalOutputValue"}
CANONICAL = REPO / "Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs"
scanner_spec = importlib.util.spec_from_file_location("jet_scanner", COQ / "scan-jet-proofs.py")
scanner = importlib.util.module_from_spec(scanner_spec)
scanner_spec.loader.exec_module(scanner)


def check(model=MODEL, canonical=CANONICAL):
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
    canonical_types = dict(re.findall(r"^\s*(\w+)\s*::\s*Prim\s+(.+)$", haskell, re.M))
    names = dict(re.findall(r'^primName\s+(\w+)\s*=\s*"([^"]+)"', haskell, re.M))
    coq_names = {}
    for match in re.finditer(r"\|\s*(\w+)\s*=>", code):
        value = re.match(r'\s*"([^"]+)"', raw[match.end():])
        if value:
            coq_names[match[1]] = value[1]
    def normalize(value):
        value = value.replace("()", "Unit").replace("PubKey", "Word256")
        value = re.sub(r"\bS\b", "Sum Unit", value)
        return re.sub(r"[\s()]", "", value)
    for constructor, signature in constructors:
        if constructor not in canonical_types or normalize(signature) != normalize(canonical_types[constructor]):
            raise ValueError(f"Bitcoin primitive type mismatch: {constructor}")
        if coq_names.get(constructor) != names.get(constructor):
            raise ValueError(f"Bitcoin primitive name mismatch: {constructor}")
    return len(constructors)


def _haskell(canonical):
    haskell = re.sub(r"--[^\n]*", "", canonical.read_text())
    prefix = re.search(r'^primPrefix\s*=\s*"([^"]+)"', haskell, re.M)
    types = dict(re.findall(r"^\s*([A-Z]\w*)\s*::\s*Prim\s+(.+)$", haskell, re.M))
    names = dict(re.findall(r'^primName\s+(\w+)\s*=\s*"([^"]+)"', haskell, re.M))
    return (prefix[1] if prefix else None), types, names


def base_findings(base_model=BASE_MODEL, canonical=CANONICAL):
    """Every difference between the frozen base model and canonical Haskell."""
    raw = base_model.read_text()
    code = scanner.code_only(raw)
    prefix, types, names = _haskell(canonical)
    found = set()
    decl = re.search(r"\bDefinition primName\s*:\s*string\s*:=", code)
    base_prefix = re.match(r'\s*"([^"]+)"\s*\.', raw[decl.end():]) if decl else None
    if not base_prefix or base_prefix[1] != prefix:
        found.add(("namespace", "primName", base_prefix[1] if base_prefix else "", prefix or ""))
    def normalize(value):
        value = value.replace("()", "Unit").replace("PubKey", "Word256")
        value = re.sub(r"\(([^(),]+),([^(),]+)\)", r"(Prod \1 \2)", value)
        value = re.sub(r"\bS\b", "Sum Unit", value)
        return re.sub(r"[\s()]", "", value)
    base_names = {}
    for match in re.finditer(r"\|\s*(\w+)\s*=>", code):
        value = re.match(r'\s*"([^"]+)"', raw[match.end():])
        if value:
            base_names[match[1]] = value[1]
    for constructor, signature in re.findall(r"\|\s*(\w+)\s*:\s*prim\s+([^\n.]+)", code):
        if constructor in LEGACY:
            continue
        if constructor not in types:
            found.add(("constructor", constructor, signature.strip(), ""))
        elif normalize(signature) != normalize(types[constructor]):
            found.add(("type", constructor, signature.strip(), types[constructor].strip()))
        if constructor in types and base_names.get(constructor) != names.get(constructor):
            found.add(("name", constructor, base_names.get(constructor) or "", names.get(constructor) or ""))
    return found


def documented(report=MISMATCH_REPORT):
    marker = r'<!--\s*gate bitcoin-base (\w+) (\w+) "([^"]*)" "([^"]*)"\s*-->'
    return set(re.findall(marker, report.read_text()))


def check_base(base_model=BASE_MODEL, canonical=CANONICAL, report=MISMATCH_REPORT):
    found, known = base_findings(base_model, canonical), documented(report)
    undocumented, stale = sorted(found - known), sorted(known - found)
    if undocumented:
        raise ValueError("undocumented base-model mismatch(es) with canonical Haskell; report them in "
                         f"{report.name}: " + "; ".join(" ".join(x) for x in undocumented))
    if stale:
        raise ValueError(f"documented mismatch(es) no longer present; update {report.name}: "
                         + "; ".join(" ".join(x) for x in stale))
    return sorted(found)


if __name__ == "__main__":
    try:
        count = check()
        reported = check_base()
    except (OSError, ValueError) as error:
        sys.exit(str(error))
    for kind, constructor, coq, haskell in reported:
        print(f"REPORTED mismatch (not corrected): frozen base {kind} {constructor}: "
              f"Coq {coq!r}, Haskell {haskell!r} ({MISMATCH_REPORT.name})")
    print(f"Bitcoin primitive identities match canonical Haskell: {count} extended constructors; "
          f"{len(reported)} documented base-model mismatch(es)")
