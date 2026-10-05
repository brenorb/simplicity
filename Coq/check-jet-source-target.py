#!/usr/bin/env python3
"""Reject drift from the recorded production C and canonical Haskell target."""
import hashlib
import os
from pathlib import Path

COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
SUFFIXES = {"C": {".c", ".h", ".inc", ".S", ".s"}, "Haskell": {".hs"}}
EXCLUDED = {"C/test.c"}  # Test harness, absent from every proof translation unit.
CONFIG_INPUTS = {'Coq/C/regenerate-bitcoin-jets.sh', 'Coq/C/jet_translation_unit.c', 'Coq/C/clightgen-linux.ini.in', 'Coq/C/jet_bitcoin_translation_unit.c', 'Coq/C/regenerate-secp-jets.sh', 'Coq/C/jet_secp_translation_unit.c', 'Coq/C/regenerate-sha-jets.sh', 'Coq/C/regenerate-jets.sh', 'Coq/C/jet_sha_translation_unit.c'}


def check(repo=REPO, manifest=COQ / "C/jet_source_target.tsv", configs=CONFIG_INPUTS, coq=COQ):
    expected = {}
    for line in manifest.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        name, digest = line.split("\t")
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or name in expected:
            raise ValueError(f"invalid source-target entry: {name}")
        expected[name] = digest
    actual = {str(p.relative_to(repo)) for folder, suffixes in SUFFIXES.items()
              for p in (repo / folder).rglob("*") if p.is_file() and p.suffix in suffixes}
    actual |= set(configs)
    actual -= EXCLUDED
    if actual != set(expected):
        raise ValueError(f"source target file set differs: missing {sorted(set(expected) - actual)}, "
                         f"added {sorted(actual - set(expected))}")
    for name, digest in expected.items():
        path = coq / name.removeprefix("Coq/") if name.startswith("Coq/") else repo / name
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"source target changed: {name}")
    return len(expected)


if __name__ == "__main__":
    try:
        count = check()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
    print(f"production/canonical sources and generation configuration match: {count} files")
