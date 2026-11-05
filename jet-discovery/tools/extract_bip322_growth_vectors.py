#!/usr/bin/env python3
"""Inventory every vendored BIP322 row and extract the bounded keypath subset."""
import base64
import csv
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "vendor-specs/bitcoin-growth"
CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"


def taproot_key(address):
    address = address.lower()
    hrp, encoded = address.rsplit("1", 1)
    values = [CHARSET.index(c) for c in encoded]
    chk = 1
    expand = [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]
    for value in expand + values:
        top = chk >> 25
        chk = ((chk & 0x1ffffff) << 5) ^ value
        for i, generator in enumerate([0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]):
            if (top >> i) & 1:
                chk ^= generator
    assert chk == 0x2bc830a3 and values[0] == 1 and hrp == "bc", "Not mainnet P2TR bech32m"
    acc = bits = 0
    decoded = bytearray()
    for value in values[1:-6]:
        acc = (acc << 5) | value
        bits += 5
        while bits >= 8:
            bits -= 8
            decoded.append((acc >> bits) & 255)
    assert bits < 5 and (acc & ((1 << bits) - 1)) == 0 and len(decoded) == 32
    return bytes(decoded)


def main():
    inventory, eligible, sources = [], [], []
    for filename in ["bip322-basic-vectors.json", "bip322-generated-vectors.json"]:
        raw = (DATA / filename).read_bytes()
        sources.append({"file": filename, "sha256": hashlib.sha256(raw).hexdigest()})
        document = json.loads(raw)
        for section, rows in document.items():
            assert isinstance(rows, list), "Unexpected upstream section"
            for index, row in enumerate(rows):
                ident = filename.removesuffix(".json") + ":" + section + ":" + str(index)
                address = row.get("address", "")
                signatures = row.get("bip322_signatures", [row["signature"]] if "signature" in row else [])
                decision = "outside supported bounded P2TR-keypath SIMPLE subset"
                count = 0
                if section in ("simple", "error") and address.startswith("bc1p"):
                    key = taproot_key(address)
                    for sig_index, signature in enumerate(signatures):
                        if signature.startswith("ful"):
                            continue
                        encoded = signature[3:] if signature.startswith("smp") else signature
                        try:
                            proof = base64.b64decode(encoded, validate=True)
                        except ValueError:
                            continue
                        if len(proof) != 66 or proof[:2] != bytes([1, 64]):
                            continue
                        eligible.append(dict(case_id=ident + ":sig" + str(sig_index), message_hex=row["message"].encode().hex(),
                                             key_hex=key.hex(), signature_hex=proof[2:].hex(), expected="Reject" if section == "error" else "Accept"))
                        count += 1
                    decision = "bounded kernel exercised" if count else "P2TR row requires full/other proof-format parsing outside bound"
                inventory.append(dict(case_id=ident, section=section, type=row.get("type", ""), address=address,
                                      signature_count=len(signatures), exercised_signatures=count, decision=decision))
    assert len(inventory) == 60 and len(eligible) == 4, "Upstream vector shape changed; re-audit complete coverage"
    for name, rows in [("bip322-vector-inventory.tsv", inventory), ("bip322-keypath-vectors.tsv", eligible)]:
        with (DATA / name).open("w", newline="") as destination:
            writer = csv.DictWriter(destination, rows[0].keys(), delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)
    (DATA / "bip322-vector-coverage.json").write_text(json.dumps(dict(sources=sources, upstream_rows=len(inventory),
        exercised_signatures=len(eligible), accepted=2, rejected=2,
        boundary="Canonical decoded one-element/64-byte keypath witness and decoded mainnet P2TR key. Bech32m/Base64/UI prefix handling is a client boundary, not a Simplicity claim."), indent=2) + "\n")
    print("Inventoried all 60 upstream rows; extracted 2 valid and 2 invalid P2TR SIMPLE signature cases")


if __name__ == "__main__":
    main()
