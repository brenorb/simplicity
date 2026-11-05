#!/usr/bin/env python3
"""Refresh the pinned BIP inventory. Downloads are data, never executed.

Run from any directory. The revision is deliberately immutable; updating it
requires reviewing the complete triage table against the new index.
"""
import argparse
import concurrent.futures
import csv
import hashlib
import json
from pathlib import Path
import re
import urllib.request

REVISION = "a0c977f3755da6476b955677ca9318334a2432c4"
ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / "vendor-specs" / "bip-inventory"
TERMINAL = {"Closed", "Deployed", "Rejected", "Withdrawn", "Replaced", "Final"}
DATA_EXTENSIONS = {".md", ".mediawiki", ".json", ".csv", ".txt", ".hex"}


def fetch(url):
    request = urllib.request.Request(url, headers={"User-Agent": "simplicity-jet-discovery-source-audit"})
    with urllib.request.urlopen(request, timeout=60) as response:
        return response.read()


def index_rows(data):
    rows = []
    for block in data.decode().split("|-"):
        block = block.split("\n|}")[0]
        cells = [cell.strip() for cell in block.split("\n|")[1:]]
        if len(cells) != 6:
            continue
        match = re.fullmatch(r"\[\[([^|]+)\|(\d+)\]\]", cells[0])
        if match:
            rows.append(dict(path=match[1], number=int(match[2]), layer=cells[1],
                             title=cells[2], owner=cells[3], type=cells[4], status=cells[5]))
        elif cells[0].isdigit():
            rows.append(dict(path="", number=int(cells[0]), layer=cells[1],
                             title=cells[2], owner=cells[3], type=cells[4], status=cells[5]))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--offline", action="store_true", help="audit existing snapshot without network")
    args = parser.parse_args()
    DEST.mkdir(parents=True, exist_ok=True)
    if not args.offline:
        (DEST / "README.mediawiki").write_bytes(fetch(f"https://raw.githubusercontent.com/bitcoin/bips/{REVISION}/README.mediawiki"))
        (DEST / "tree.json").write_bytes(fetch(f"https://api.github.com/repos/bitcoin/bips/git/trees/{REVISION}?recursive=1"))
    rows = index_rows((DEST / "README.mediawiki").read_bytes())
    selected = [r for r in rows if r["layer"] == "Consensus (soft fork)" and r["status"] not in TERMINAL]
    tree = json.loads((DEST / "tree.json").read_text())
    if tree.get("truncated"):
        raise RuntimeError("GitHub tree is truncated; cannot claim complete coverage")
    selected_paths = {r["path"] for r in selected}
    selected_dirs = {r["path"].split(".")[0] + "/" for r in selected}
    assets = [item for item in tree["tree"] if item["type"] == "blob" and
              (item["path"] in selected_paths or
               (any(item["path"].startswith(prefix) for prefix in selected_dirs) and
                Path(item["path"]).suffix in DATA_EXTENSIONS))]

    def get_asset(item):
        path = DEST / "upstream" / item["path"]
        if not args.offline:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(fetch(f"https://raw.githubusercontent.com/bitcoin/bips/{REVISION}/{item['path']}"))
        content = path.read_bytes()
        # The API's git object hash verifies bytes independently of our SHA-256.
        git_hash = hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()
        if git_hash != item["sha"]:
            raise RuntimeError(f"upstream blob hash mismatch: {item['path']}")
        return dict(path=item["path"], blob_sha1=git_hash, sha256=hashlib.sha256(content).hexdigest(),
                    bytes=len(content), source=f"https://raw.githubusercontent.com/bitcoin/bips/{REVISION}/{item['path']}")

    with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:
        manifest = sorted(pool.map(get_asset, assets), key=lambda x: x["path"])
    licenses = {}
    for row in selected:
        text = (DEST / "upstream" / row["path"]).read_text()
        matches = re.findall(r"^\s*License:\s*(.+)$", text, re.MULTILINE)
        licenses[row["path"].split(".")[0]] = "; ".join(matches) or "Not stated in BIP header; see copyright section"
    for asset in manifest:
        key = asset["path"].split("/")[0].split(".")[0]
        asset["license"] = licenses[key]
    snapshot = dict(repository="https://github.com/bitcoin/bips", revision=REVISION,
                    retrieved_date="2026-11-04", index_rows=len(rows),
                    softfork_rows=sum(r["layer"] == "Consensus (soft fork)" for r in rows),
                    open_softfork_rows=len(selected), files=manifest)
    (DEST / "manifest.json").write_text(json.dumps(snapshot, indent=2) + "\n")
    with (DEST / "index-all.tsv").open("w") as f:
        writer = csv.DictWriter(f, fieldnames=["number", "path", "layer", "title", "owner", "type", "status"], delimiter="\t")
        writer.writeheader()
        writer.writerows(rows)
    print(f"Audited {len(rows)} indexed BIPs, {snapshot['softfork_rows']} softfork rows, "
          f"{len(selected)} nonterminal softfork rows, {len(manifest)} vendored data files")


if __name__ == "__main__":
    main()
