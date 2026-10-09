#!/usr/bin/env python3
"""Read-only replay of continuation repairs; not a Coq acceptance check."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def check(tree):
    candidate = json.loads((ARCHIVE / "manifest.json").read_text())["candidate_commit"]
    journal = (ARCHIVE / "CONTINUATION.md").read_text()
    patches = sorted(ARCHIVE.glob("*-repair.patch"))
    receipts = {}
    for patch in patches:
        mention = journal.index(f"`{patch.name}`")
        receipt = re.search(r"SHA-256(?: is|:)?\s*`([a-f0-9]{64})`",
                            journal[mention:mention + 2000])
        if receipt is None:
            raise ValueError(f"missing hash receipt: {patch.name}")
        receipts[patch.name] = receipt[1]
    seen = set()
    for patch in patches:
        raw = patch.read_bytes()
        if hashlib.sha256(raw).hexdigest() != receipts[patch.name]:
            raise ValueError(f"hash mismatch: {patch.name}")
        subprocess.run(["git", "apply", "--reverse", "--check", str(patch)],
                       cwd=tree, check=True)
        sections = re.split(r"(?m)^diff --git ", raw.decode())[1:]
        for section in sections:
            header = section.splitlines()[0]
            match = re.fullmatch(r"a/(Coq/C/[^ ]+\.v) b/\1", header)
            if match is None:
                raise ValueError(f"unsupported patch target: {header}")
            name = match[1]
            if name in seen:
                raise ValueError(f"overlapping repair target: {name}")
            seen.add(name)
            original = subprocess.check_output(
                ["git", "show", f"{candidate}:{name}"], cwd=REPO).decode()
            lines = original.splitlines()
            delta = 0
            hunks = re.split(r"(?m)^@@ ", section)[1:]
            for hunk in hunks:
                hheader, body = hunk.split("\n", 1)
                numbers = re.match(r"-(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", hheader)
                if numbers is None:
                    raise ValueError(f"invalid hunk: {hheader}")
                old, new = [], []
                for line in body.splitlines():
                    if line.startswith("\\ No newline"):
                        continue
                    if not line or line[0] not in " +-":
                        raise ValueError(f"invalid hunk line in {patch.name}")
                    if line[0] in " -":
                        old.append(line[1:])
                    if line[0] in " +":
                        new.append(line[1:])
                if len(old) != int(numbers[2] or 1) or len(new) != int(numbers[4] or 1):
                    raise ValueError(f"hunk count mismatch: {patch.name}")
                pos = int(numbers[1]) - 1 + delta
                if lines[pos:pos + len(old)] != old:
                    matches = [i for i in range(len(lines) - len(old) + 1)
                               if lines[i:i + len(old)] == old]
                    if len(matches) != 1:
                        raise ValueError(f"nonunique/missing hunk context: {name}")
                    pos = matches[0]
                lines[pos:pos + len(old)] = new
                delta += len(new) - len(old)
            # Repairs preserve the source's original terminal-newline convention.
            replay = "\n".join(lines) + ("\n" if original.endswith("\n") else "")
            if replay.encode() != (tree / name).read_bytes():
                raise ValueError(f"forward replay differs: {name}")
    print(f"continuation hashes, reverse checks and exact forward replay pass: "
          f"{len(patches)} patches, {len(seen)} sources")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("tree", type=Path, help="isolated repaired candidate checkout")
    check(parser.parse_args().tree.resolve())
