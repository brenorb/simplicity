#!/usr/bin/env python3
"""Offline check of primary and derived growth5 source/data packet hashes."""
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parents[1]
packet = root / "vendor-specs/bitcoin-growth5"
primary_bytes = (packet / "manifest.json").read_bytes()
primary = json.loads(primary_bytes)
derived = json.loads((packet / "derived-manifest.json").read_text())
assert derived["source_manifest_sha256"] == hashlib.sha256(primary_bytes).hexdigest()
covered = set()
for record in primary + derived["records"]:
    path = packet / record["file"]
    data = path.read_bytes()
    assert len(data) == record["bytes"], path
    assert hashlib.sha256(data).hexdigest() == record["sha256"], path
    covered.add(path.name)
    for source in record.get("source_hashes", []):
        assert hashlib.sha256((packet / source["file"]).read_bytes()).hexdigest() == source["sha256"], source["file"]
for path in packet.iterdir():
    if path.is_file():
        assert path.name in covered | {"manifest.json", "derived-manifest.json"}, path
        if path.suffix == ".tsv":
            assert b"\r" not in path.read_bytes(), path
print(f"PASS {len(primary)} primary files and {len(derived['records'])} local derived/access files; complete packet coverage and LF TSVs")
