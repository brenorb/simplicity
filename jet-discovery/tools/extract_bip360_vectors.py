#!/usr/bin/env python3
"""Validate every BIP360 construction case and derive leaf-opening TSV data.

Only Python's standard library is used. No vendored code is imported/executed.
The TSV has a separate row for every leaf in every successful upstream tree.
Wallet address encodings and execution of the enclosed Tapscripts are outside
this check: it validates construction roots, control blocks and scriptPubKeys.
"""
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "vendor-specs/bip-inventory/upstream/bip-0360/ref-impl/common/tests/data"


def tagged(tag, message):
    h = hashlib.sha256(tag.encode()).digest()
    return hashlib.sha256(h + h + message).digest()


def tree(t):
    if isinstance(t, list):
        assert len(t) == 2
        a, leaves_a = tree(t[0])
        b, leaves_b = tree(t[1])
        return tagged("TapBranch", min(a, b) + max(a, b)), [
            (leaf, path + [b]) for leaf, path in leaves_a] + [
            (leaf, path + [a]) for leaf, path in leaves_b]
    script = bytes.fromhex(t["script"])
    assert len(script) < 253  # true of every upstream vector, checked explicitly
    leaf = tagged("TapLeaf", bytes([t["leafVersion"], len(script)]) + script)
    return leaf, [(t, [])]


def main():
    rows = []
    counts = dict(cases=0, success_cases=0, construction_errors=0, leaf_openings=0)
    for source in sorted(SOURCE.glob("*.json")):
        for case in json.loads(source.read_text())["test_vectors"]:
            counts["cases"] += 1
            given, expected = case["given"], case["expected"]
            if "error" in expected:
                # This is a wallet constructor rejection, not a script spend.
                if "internalPubkey" in given:
                    actual = "P2MR does not support internal pubkeys"
                elif not given.get("scriptTree"):
                    actual = "P2MR requires a script tree with at least one leaf"
                else:
                    raise AssertionError(f"unhandled constructor error: {case['id']}")
                assert actual == expected["error"], case["id"]
                counts["construction_errors"] += 1
                continue
            root, leaves = tree(given["scriptTree"])
            assert root.hex() == case["intermediary"]["merkleRoot"], case["id"]
            assert "5220" + root.hex() == expected["scriptPubKey"], case["id"]
            controls = expected["scriptPathControlBlocks"]
            assert len(leaves) == len(controls), case["id"]
            for i, ((leaf, path), cb) in enumerate(zip(leaves, controls)):
                assert bytes.fromhex(cb) == bytes([leaf["leafVersion"] | 1]) + b"".join(path), case["id"]
                rows.append([source.name, case["id"], str(i), str(leaf["leafVersion"]),
                             leaf["script"], ",".join(h.hex() for h in path), expected["scriptPubKey"]])
            counts["success_cases"] += 1
    counts["leaf_openings"] = len(rows)
    dest = ROOT / "corpus/bips"
    dest.mkdir(parents=True, exist_ok=True)
    with (dest / "bip360-leaf-openings.tsv").open("w") as f:
        writer = csv.writer(f, delimiter="\t", lineterminator="\n")
        writer.writerow(["source", "id", "leaf_index", "leaf_version", "script", "path", "script_pubkey"])
        writer.writerows(rows)
    (dest / "bip360-coverage.json").write_text(json.dumps(counts, indent=2) + "\n")
    print(json.dumps(counts))


if __name__ == "__main__":
    main()
