#!/usr/bin/env python3
"""Inventory all BIP352 roles and extract the bounded mixed-input core cases."""
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "vendor-specs/bitcoin-growth"


def script_type(script):
    if len(script) == 68 and script.startswith("5120"):
        return "p2tr"
    if len(script) == 50 and script.startswith("76a914") and script.endswith("88ac"):
        return "p2pkh"
    return "other"


def main():
    raw = (DATA / "bip352-vectors.json").read_bytes()
    groups = json.loads(raw)
    inventory, selected = [], []
    for index, group in enumerate(groups):
        for role in ("sending", "receiving"):
            for subindex, row in enumerate(group[role]):
                ident = str(index) + ":" + role + ":" + str(subindex)
                inputs = row["given"]["vin"]
                types = [script_type(v["prevout"]["scriptPubKey"]["hex"]) for v in inputs]
                eligible = role == "sending" and len(inputs) == 2 and sorted(types) == ["p2pkh", "p2tr"]
                recipients = row["given"].get("recipients", [])
                outputs = row["expected"].get("outputs", [])
                eligible = eligible and len(recipients) == 1 and len(outputs) == 1 and len(outputs[0]) == 1
                if eligible:
                    tap = inputs[types.index("p2tr")]
                    legacy = inputs[types.index("p2pkh")]
                    outpoint = lambda v: (bytes.fromhex(v["txid"])[::-1] + v["vout"].to_bytes(4, "little")).hex()
                    selected.append(dict(case_id=ident, taproot_private=tap["private_key"], legacy_private=legacy["private_key"],
                        taproot_outpoint=outpoint(tap), legacy_outpoint=outpoint(legacy), scan_key=recipients[0]["scan_pub_key"],
                        spend_key=recipients[0]["spend_pub_key"], expected_shared=row["expected"]["shared_secrets"][0], expected_output=outputs[0][0]))
                inventory.append(dict(case_id=ident, comment=group["comment"], role=role, inputs=len(inputs), input_types=",".join(types),
                    decision="exercise exact mixed-input output derivation core" if eligible else "outside bounded mixed-input one-recipient sender covenant"))
    assert len(groups) == 29 and len(inventory) == 59 and len(selected) == 3, (len(groups), len(inventory), [r["case_id"] for r in selected])
    for name, rows in [("bip352-vector-inventory.tsv", inventory), ("bip352-mixed-core-vectors.tsv", selected)]:
        with (DATA / name).open("w", newline="") as out:
            writer = csv.DictWriter(out, rows[0].keys(), delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)
    (DATA / "bip352-vector-coverage.json").write_text(json.dumps(dict(source_sha256=hashlib.sha256(raw).hexdigest(), top_level_groups=29,
        inventoried_role_cases=59, selected_sender_core_cases=3,
        limitation="Upstream cases exercise exact BIP352 derivation core only. Complete native covariance/provenance and BIP374 proofs use derived, documented transactions; not all BIP352 address/scan/label modes are implemented."), indent=2) + "\n")
    print("Inventoried all 29 groups / 59 role cases; extracted all three exact mixed-input derivation cases")


if __name__ == "__main__":
    main()
