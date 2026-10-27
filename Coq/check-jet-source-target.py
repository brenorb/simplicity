#!/usr/bin/env python3
"""Reject drift in frozen production, specifications, ASTs and generation inputs."""
import hashlib
import os
import re
from pathlib import Path

COQ = Path(__file__).resolve().parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
SUFFIXES = {"C": {".c", ".h", ".inc", ".S", ".s"}, "Haskell": {".hs"}}
EXCLUDED = {"C/test.c"}  # Test harness, absent from every proof translation unit.
# Protect the specification tree itself: types, domains, semantics and primitive
# identities are definitions here, not just in the canonical Haskell sources.
COQ_TREES = {"Simplicity": {".v"}}
COQ_PATTERNS = (
    "C/jets*.v", "C/memcpy_*.v", "C/*translation_unit.c",
    "C/jet_memcpy_*.c", "C/clightgen*.in", "C/regenerate-*.sh",
)
MANIFEST_SHA256 = "8ba2f4d48470b988eab2de57ec2cbc79604b3c368d517f368a036093f5d43896"
CONFIG_INPUTS = {"Coq/jet-deps.sh", "Coq/jet-sysroot.sh"}


def protected_coq_files(coq):
    names = {f"Coq/{p.relative_to(coq)}"
             for folder, suffixes in COQ_TREES.items()
             for p in (coq / folder).rglob("*")
             if p.is_file() and p.suffix in suffixes}
    names |= {f"Coq/{p.relative_to(coq)}"
              for pattern in COQ_PATTERNS for p in coq.glob(pattern)
              if p.is_file()}
    return names


def check(repo=REPO, manifest=COQ / "C/jet_source_target.tsv", configs=None, coq=COQ):
    if manifest == COQ / "C/jet_source_target.tsv":
        if hashlib.sha256(manifest.read_bytes()).hexdigest() != MANIFEST_SHA256:
            raise ValueError("frozen source-target manifest changed; baseline updates require separate approval")
    expected = {}
    for line in manifest.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        name, digest = line.split("\t")
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise ValueError(f"invalid source-target digest: {name}")
        path = Path(name)
        if path.is_absolute() or ".." in path.parts or name in expected:
            raise ValueError(f"invalid source-target entry: {name}")
        expected[name] = digest
    actual = {str(p.relative_to(repo)) for folder, suffixes in SUFFIXES.items()
              for p in (repo / folder).rglob("*") if p.is_file() and p.suffix in suffixes}
    if configs is None:
        actual |= protected_coq_files(coq) | CONFIG_INPUTS
    else:
        actual |= set(configs)
    actual -= EXCLUDED
    if actual != set(expected):
        raise ValueError(f"source target file set differs: missing {sorted(set(expected) - actual)}, "
                         f"added {sorted(actual - set(expected))}")
    for name, digest in expected.items():
        path = coq / name.removeprefix("Coq/") if name.startswith("Coq/") else repo / name
        if path.is_symlink():
            raise ValueError(f"source target is a symlink: {name}")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"source target changed: {name}")
    return len(expected)


if __name__ == "__main__":
    try:
        count = check()
    except (ValueError, OSError) as error:
        raise SystemExit(str(error))
    print(f"frozen production/specification/AST/generation inputs match: {count} files")
