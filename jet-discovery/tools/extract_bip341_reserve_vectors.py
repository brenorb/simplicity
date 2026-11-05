#!/usr/bin/env python3
"""Inventory every published BIP341 signing case; extract ALL01/no-annex cases.

This reads published JSON as data and never runs upstream code. It does not
claim the bounded BIP127 application supports every BIP341 signing mode.
"""
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "vendor-specs/bitcoin-growth2"
SOURCE = OUT / "bip-0341-wallet-test-vectors.json"


def write_tsv(path, columns, rows):
    with path.open("w", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(columns)
        writer.writerows(rows)


def main():
    source = json.loads(SOURCE.read_text())
    cases = []
    compatible = []
    for group_index, group in enumerate(source["keyPathSpending"]):
        prefix = f"bip341-group-{group_index}"
        (OUT / f"{prefix}-unsigned.hex").write_text(group["given"]["rawUnsignedTx"] + "\n")
        write_tsv(OUT / f"{prefix}-utxos.tsv", ["index", "amount_sat", "script_pubkey"],
                  [(i, u["amountSats"], u["scriptPubKey"]) for i, u in enumerate(group["given"]["utxosSpent"])])
        for case_index, case in enumerate(group["inputSpending"]):
            given = case["given"]
            supported = given["hashType"] == 1
            cases.append([group_index, case_index, given["txinIndex"], given["hashType"],
                          "ALL01/no-annex digest reference" if supported else "other sighash mode outside this bounded reference"])
            if supported:
                witness, = case["expected"]["witness"]
                assert len(bytes.fromhex(witness)) == 65 and witness[-2:] == "01"
                compatible.append([group_index, case_index, given["txinIndex"],
                                   case["intermediary"]["sigHash"], witness[:-2]])
    assert len(cases) == 7 and len(compatible) == 1
    write_tsv(OUT / "bip341-signing-inventory.tsv", ["group", "case", "input_index", "hash_type", "coverage"], cases)
    write_tsv(OUT / "bip341-all01-vectors.tsv", ["group", "case", "input_index", "expected_digest", "signature64"], compatible)
    (OUT / "bip341-reserve-coverage.json").write_text(json.dumps({
        "source": SOURCE.name, "keypath_groups": len(source["keyPathSpending"]),
        "all_signing_cases": len(cases), "all01_reference_cases": len(compatible),
        "other_signing_cases": len(cases)-len(compatible),
        "script_pubkey_vector_cases": len(source["scriptPubKey"]),
        "scope": "BIP341 byte-oriented ALL01/no-annex reference validation; BIP127 itself has no published official transaction vectors in the pinned specification"
    }, indent=2) + "\n")
    print(f"Inventoried all {len(cases)} BIP341 signing cases; extracted {len(compatible)} compatible ALL01 case")


if __name__ == "__main__":
    main()
