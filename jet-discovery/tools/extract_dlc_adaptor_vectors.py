#!/usr/bin/env python3
"""Lossless row inventory of all pinned ECDSA-adaptor data cases; no upstream code."""
import csv
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
source = root / "vendor-specs/bitcoin-growth/dlc-ecdsa-adaptor-vectors.json"
target = root / "vendor-specs/bitcoin-growth2/dlc-adaptor-all-vectors.tsv"
cases = json.loads(source.read_text())
columns = ["case", "kind", "adaptor_sig", "message_hash", "public_signing_key", "encryption_key", "decryption_key", "signature", "error", "comment"]
with target.open("w", newline="") as out:
    writer = csv.writer(out, delimiter="\t", lineterminator="\n")
    writer.writerow(columns)
    for i, case in enumerate(cases):
        writer.writerow([i] + [case.get(field) or "-" for field in columns[1:]])
assert len(cases) == 11
print("Extracted all11 cases:3verification,3recovery,5serialization")

bip143 = (root / "vendor-specs/bitcoin-growth2/bip-0143.mediawiki").read_text()
section = ""
rows = []
for line in bip143.splitlines():
    if line.startswith("==="):
        section = line.strip("= ")
    match = re.search(r"sigHash:\s+([0-9a-f]{64})", line)
    if match:
        rows.append([len(rows), section, match.group(1),
                     "one complete ALL01 six-of-six reference cross-check" if match.group(1).startswith("185c0be5") else "not claimed as a complete numeric-DLC fixture"])
with (target.parent / "bip143-inline-digest-inventory.tsv").open("w", newline="") as out:
    writer = csv.writer(out, delimiter="\t", lineterminator="\n")
    writer.writerow(["case", "source_section", "digest", "coverage"])
    writer.writerows(rows)
native = bip143.split("=== P2SH-P2WSH ===", 1)[1].split("=== No FindAndDelete ===", 1)[0]
raw = re.search(r"unsigned transaction: ([0-9a-f]+)", native).group(1)
script = re.search(r"witnessScript: ([0-9a-f]+)", native).group(1)
expected = re.search(r"sigHash:\s+([0-9a-f]{64})", native).group(1)
(target.parent / "bip143-all01-crosscheck.tsv").write_text(
    "raw_unsigned\tamount_sat\twitness_script\texpected_digest\n" +
    "\t".join([raw, "987654321", script, expected]) + "\n")
print(f"Inventoried all {len(rows)} explicitly named BIP143 inline digests; extracted one ALL01 reference cross-check")
