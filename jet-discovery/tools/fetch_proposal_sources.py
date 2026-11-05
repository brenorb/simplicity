#!/usr/bin/env python3
"""Fetch/audit the exact proposal response snapshots listed in sources.json.

Mutable sources can legitimately change. A differing response is rejected and
never overwrites the saved snapshot; review it and its revision metadata before
changing the manifest. Downloaded material is data, never executed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import urllib.request

DEST = Path(__file__).resolve().parents[1] / "vendor-specs/bip-inventory/proposals"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true")
    args = parser.parse_args()
    entries = json.loads((DEST / "sources.json").read_text())["files"]
    for entry in entries:
        if args.offline:
            data = (DEST / entry["path"]).read_bytes()
        else:
            request = urllib.request.Request(entry["url"], headers={"User-Agent": "simplicity-jet-discovery-source-audit"})
            with urllib.request.urlopen(request, timeout=60) as response:
                data = response.read()
        digest = hashlib.sha256(data).hexdigest()
        if digest != entry["sha256"] or len(data) != entry["bytes"]:
            raise RuntimeError(f"source changed or local bytes corrupted: {entry['path']} (expected {entry['sha256']}, got {digest}); saved snapshot is untouched")
        if not args.offline:
            (DEST / entry["path"]).write_bytes(data)
    print(f"Verified all {len(entries)} proposal source snapshots")


if __name__ == "__main__":
    main()
