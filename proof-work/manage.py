#!/usr/bin/env python3
"""Verify preserved sources and patch replay, or extract sources outside the repo.

This checks archive integrity. It neither compiles nor accepts a Coq proof.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
REPO = HERE.parent
SOURCE_GROUPS = ("scalar-u128", "sha-support", "review-witnesses")


def git(*args, env=None):
    return subprocess.check_output(
        ["git", "-C", str(REPO), *args], env=env, stderr=subprocess.PIPE
    ).decode().strip()


def read_manifest(group):
    return json.loads((HERE / group / "manifest.json").read_text())


def check_hash(path, expected):
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"source hash mismatch: {path.relative_to(HERE)}")


def verify_sources():
    count = 0
    for group in SOURCE_GROUPS:
        manifest = read_manifest(group)
        git("cat-file", "-e", manifest["dependency_base_commit"] + "^{commit}")
        for record in manifest["files"]:
            check_hash(HERE / group / record["path"], record["sha256"])
            count += 1
    inventory = json.loads((HERE / "scratch-inventory.json").read_text())
    if len(inventory["entries"]) != 84:
        raise ValueError("incomplete scratch inventory")
    for record in inventory["entries"]:
        location = record.get("location")
        if location and location.endswith(".source"):
            check_hash(REPO / location, record["source_sha256"])
        if "integrated_blob" in record:
            current = git("rev-parse", "HEAD:" + location)
            if current != record["integrated_blob"]:
                raise ValueError(f"integrated source changed: {location}")
    print(f"{count} archived sources/checkers match their hashes; 84 scratch files accounted for")


def replay(group):
    manifest = read_manifest(group)
    if group == "range":
        patches = manifest["patches"]
    else:
        patches = [{
            "path": "candidate.patch",
            "sha256": manifest["patch_sha256"],
            "commit": manifest["candidate_commit"],
        }]
    # A separate index prevents touching the user's index or working tree.
    # Git may store reconstructed blob/tree objects in its object database.
    with tempfile.TemporaryDirectory(prefix="simplicity-proof-replay-") as temp:
        env = dict(os.environ, GIT_INDEX_FILE=str(Path(temp) / "index"))
        git("read-tree", manifest["base_commit"], env=env)
        for patch in patches:
            path = HERE / group / patch["path"]
            check_hash(path, patch["sha256"])
            git("apply", "--cached", "--whitespace=nowarn", str(path), env=env)
            actual = git("write-tree", env=env)
            expected = git("rev-parse", patch["commit"] + "^{tree}")
            if actual != expected:
                raise ValueError(f"patch replay changed the candidate tree: {path.name}")
    print(f"{group}: {len(patches)} patches reproduce every recorded candidate tree exactly")


def extract(group, output):
    destination = Path(output).resolve()
    if destination == REPO or REPO in destination.parents:
        raise ValueError("extract to an external directory, outside the repository")
    if destination.exists():
        raise ValueError("output directory must not exist; existing work will not be overwritten")
    manifest = read_manifest(group)
    files = []
    for record in manifest["files"]:
        name = record["materialized_name"]
        if Path(name).name != name:
            raise ValueError(f"invalid materialized filename: {name}")
        path = HERE / group / record["path"]
        check_hash(path, record["sha256"])
        files.append((name, path.read_bytes()))
    destination.mkdir(parents=True)
    for name, source in files:
        (destination / name).write_bytes(source)
    print(f"Extracted {len(files)} exact sources to {destination}; compilation/acceptance remains pending")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extract", choices=SOURCE_GROUPS)
    parser.add_argument("--output")
    args = parser.parse_args()
    if args.extract:
        if not args.output:
            parser.error("--extract requires --output")
        extract(args.extract, args.output)
    else:
        if args.output:
            parser.error("--output requires --extract")
        verify_sources()
        replay("range")
        replay("secp-field-predicates")


if __name__ == "__main__":
    main()
