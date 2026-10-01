#!/usr/bin/env python3
"""Inventory every public C jet, without conflating helper proofs with coverage.

Proof entries are metadata pointing to frozen, audited public theorem types.
This script does not check proofs: run check-jets.sh for that. CSV lists every
declaration, including missing proofs, unregistered jets and legacy names.
"""
import argparse
import csv
import os
import re
import sys
from collections import Counter
from pathlib import Path

from importlib.util import module_from_spec, spec_from_file_location

sys.dont_write_bytecode = True
COQ = Path(__file__).resolve().parent
# The Nix proof derivations build an isolated Coq source tree. Supply the
# independently filtered, read-only C inventory there; normal checkouts need
# no override. Missing headers are an error, never silently reduced scope.
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
HEADERS = {
    "core": "C/jets.h",
    "bitcoin": "C/bitcoin/bitcoinJets.h",
    "elements": "C/elements/elementsJets.h",
}
SPECIFICATIONS = {
    "core": "Haskell/Core/Simplicity/CoreJets.hs",
    "bitcoin": "Haskell/Simplicity/Bitcoin/Jets.hs",
    "elements": "Haskell/Simplicity/Elements/Jets.hs",
}


def records(path, fields):
    result = []
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        row = line.split()
        if len(row) != fields:
            raise ValueError(f"{path}:{number}: expected {fields} fields")
        result.append(row)
    return result


def declarations(source):
    source = re.sub(r"/\*.*?\*/|//[^\n]*", "", source, flags=re.S)
    decls = re.findall(r"\bbool\s+(simplicity_\w+)\s*\(([^;{}]*)\)\s*;", source)
    names = []
    for name, args in decls:
        args = re.sub(r"\s+", "", args)
        if args != "frameItem*dst,frameItemsrc,consttxEnv*env":
            raise ValueError(f"unexpected public jet signature for {name}: {args}")
        names.append(name)
    return names


def inventory():
    jets = {}
    for family, header in HEADERS.items():
        for name in declarations((REPO / header).read_text()):
            if name in jets:
                raise ValueError(f"duplicate public jet: {name}")
            jets[name] = {"family": family, "function": name, "header": header,
                          "specification_catalog": SPECIFICATIONS[family],
                          "registrations": [], "proof": ""}
    for application in ("bitcoin", "elements"):
        registry = REPO / f"C/{application}/primitiveJetNode.inc"
        source = registry.read_text()
        nodes = re.findall(r"\[(\w+)\]\s*=\s*\{(.*?)\n\}", source, re.S)
        parsed_functions = []
        for identifier, body in nodes:
            match = re.search(r"\.jet\s*=\s*(simplicity_\w+)", body)
            if not match:
                raise ValueError(f"unparsed jet node: {registry}:{identifier}")
            name = match[1]
            if name not in jets:
                raise ValueError(f"registered jet lacks public declaration: {name}")
            jets[name]["registrations"].append(f"{application}:{identifier}")
            parsed_functions.append(name)
        if Counter(parsed_functions) != Counter(re.findall(r"\.jet\s*=\s*(simplicity_\w+)", source)):
            raise ValueError(f"registry parser missed entries: {registry}")
    audited = {tuple(row) for row in records(COQ / "C/jet_public_theorems.txt", 2)}
    scanner_spec = spec_from_file_location("jet_scanner", COQ / "scan-jet-proofs.py")
    scanner = module_from_spec(scanner_spec)
    scanner_spec.loader.exec_module(scanner)
    for name, module, theorem in records(COQ / "C/jet_coverage.tsv", 3):
        if name not in jets:
            raise ValueError(f"proof entry for unknown jet: {name}")
        if jets[name]["proof"]:
            raise ValueError(f"duplicate coverage entry: {name}")
        if (module, theorem) not in audited:
            raise ValueError(f"coverage theorem not publicly audited: {module}.{theorem}")
        code = scanner.code_only((COQ / (module.replace(".", "/") + ".v")).read_text())
        statement = re.search(rf"\b(?:Theorem|Lemma|Corollary)\s+{re.escape(theorem)}\s*:(.*?)\bProof\.", code, re.S)
        if not statement or not re.search(rf"\bjet_local_spec\s+f_{re.escape(name)}\b", statement[1]):
            raise ValueError(f"coverage entry is not a direct canonical jet theorem: {module}.{theorem}")
        jets[name]["proof"] = f"{module}.{theorem}"
    return list(jets.values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--csv", action="store_true", help="list every jet, including all missing proofs")
    parser.add_argument("--require-complete", action="store_true", help="fail if ANY declared jet lacks coverage")
    args = parser.parse_args()
    try:
        jets = inventory()
    except (ValueError, OSError) as error:
        sys.exit(str(error))
    if args.csv:
        writer = csv.DictWriter(sys.stdout, fieldnames=list(jets[0]))
        writer.writeheader()
        for row in jets:
            writer.writerow({**row, "registrations": ";".join(row["registrations"])})
    else:
        for family in HEADERS:
            rows = [row for row in jets if row["family"] == family]
            print(f"{family}: {sum(bool(row['proof']) for row in rows)}/{len(rows)} jets have audited proof entries")
        missing = sum(not row["proof"] for row in jets)
        unregistered = sum(not row["registrations"] for row in jets)
        print(f"total: {len(jets) - missing}/{len(jets)}; remaining: {missing}; unregistered declarations: {unregistered}")
        print("Scope: public jet declarations in all three C headers. Proof validity requires check-jets.sh.")
    if args.require_complete and any(not row["proof"] for row in jets):
        sys.exit("Every-jet goal is incomplete: declared C jets still lack proofs.")


if __name__ == "__main__":
    main()
