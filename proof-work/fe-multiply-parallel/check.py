#!/usr/bin/env python3
"""Check or extract the archived parallel fe_multiply/fe_square sources.

    python3 -I proof-work/fe-multiply-parallel/check.py
    python3 -I proof-work/fe-multiply-parallel/check.py --extract /new/external/dir

The check compares every archived source with its manifest hash. Extraction
writes the materialized .v names (proof modules and pinned negation sources)
into a new directory outside the repository. Neither compiles nor accepts them;
use verify.sh for a fresh build and kernel check.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
MANIFESTS = (HERE / "modules" / "modules-manifest.json",
             HERE / "negate-dependency" / "fe-negate-manifest.json")


def sources():
    for manifest in MANIFESTS:
        for record in json.loads(manifest.read_text())["files"]:
            # The negation manifest also lists its checkers; only the
            # Coq sources were pinned (see negate-dependency/README.md).
            if not record["path"].endswith(".v.source"):
                continue
            path = manifest.parent / record["path"]
            data = path.read_bytes()
            if hashlib.sha256(data).hexdigest() != record["sha256"]:
                raise ValueError(f"hash mismatch: {path.relative_to(REPO)}")
            name = record["materialized_name"]
            if Path(name).name != name:
                raise ValueError(f"invalid materialized filename: {name}")
            yield name, data


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--extract", metavar="DIR")
    args = parser.parse_args()
    files = list(sources())
    if not args.extract:
        print(f"{len(files)} archived sources match their manifest hashes")
        return
    destination = Path(args.extract).resolve()
    if destination == REPO or REPO in destination.parents:
        raise ValueError("extract to an external directory, outside the repository")
    if destination.exists():
        raise ValueError("output directory must not exist")
    destination.mkdir(parents=True)
    for name, data in files:
        (destination / name).write_bytes(data)
    print(f"Extracted {len(files)} exact sources to {destination}")


if __name__ == "__main__":
    main()
