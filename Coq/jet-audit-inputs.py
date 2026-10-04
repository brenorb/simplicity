#!/usr/bin/env python3
"""Fingerprint source inputs so an audit cannot accept an edited working tree."""
import argparse
import hashlib
import os
from pathlib import Path

COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
SNAPSHOTS = {"jet_assumptions.expected", "jet_contracts.expected", "jet_coqchk_axioms.expected"}


def fingerprint(coq=COQ, repo=REPO, updating=False):
    digest = hashlib.sha256()
    for label, root, suffixes in (
        ("Coq", coq, {".v", ".sh", ".py", ".txt", ".tsv", ".expected"}),
        ("C", repo / "C", {".c", ".h", ".inc"}),
        ("Haskell", repo / "Haskell", {".hs"}),
    ):
        for path in sorted(root.rglob("*")):
            if not path.is_file() or "__pycache__" in path.parts:
                continue
            if path.suffix not in suffixes and not path.name.startswith("_CoqProject"):
                continue
            if updating and label == "Coq" and path.name in SNAPSHOTS:
                continue
            name = f"{label}/{path.relative_to(root)}".encode()
            content = path.read_bytes()
            for part in (name, content):
                digest.update(len(part).to_bytes(8, "big"))
                digest.update(part)
    return digest.hexdigest()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--updating", action="store_true")
    args = parser.parse_args()
    print(fingerprint(updating=args.updating))
