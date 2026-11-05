#!/usr/bin/env python3
"""Parse all of real Bitcoin block 170 and derive its two-leaf receipt proof.

Only local data is read. No downloaded implementation is executed.
"""
import hashlib
import json
import struct
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "vendor-specs/spv"
DEST = ROOT / "vendor-specs/bitcoin-growth"


def sha256d(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def parse_transaction(block, start):
    pos = start
    version, = struct.unpack_from("<I", block, pos)
    pos += 4

    def compact():
        nonlocal pos
        first = block[pos]
        pos += 1
        if first < 253:
            return first
        width = {253: 2, 254: 4, 255: 8}[first]
        result = int.from_bytes(block[pos:pos + width], "little")
        pos += width
        assert result >= {253: 253, 254: 65536, 255: 4294967296}[first]
        return result

    inputs = []
    for _ in range(compact()):
        previous_hash = block[pos:pos + 32]
        pos += 32
        previous_index, = struct.unpack_from("<I", block, pos)
        pos += 4
        length = compact()
        script = block[pos:pos + length]
        pos += length
        sequence, = struct.unpack_from("<I", block, pos)
        pos += 4
        inputs.append(dict(previous_hash=previous_hash, previous_index=previous_index, script=script, sequence=sequence))
    outputs = []
    for _ in range(compact()):
        value, = struct.unpack_from("<Q", block, pos)
        pos += 8
        length = compact()
        script = block[pos:pos + length]
        pos += length
        outputs.append(dict(value=value, script=script))
    lock, = struct.unpack_from("<I", block, pos)
    pos += 4
    return dict(version=version, inputs=inputs, outputs=outputs, lock=lock, raw=block[start:pos]), pos


def main():
    block = (SOURCE / "mainnet-170.block").read_bytes()
    headers = [bytes.fromhex((SOURCE / ("mainnet-" + str(height) + ".header.hex")).read_text().strip()) for height in [169, 170, 171]]
    assert all(len(h) == 80 for h in headers)
    assert block[:80] == headers[1] and block[80] == 2
    transactions, pos = [], 81
    for _ in range(2):
        tx, pos = parse_transaction(block, pos)
        transactions.append(tx)
    assert pos == len(block), "Full block not consumed"
    txids = [sha256d(tx["raw"]) for tx in transactions]
    assert sha256d(txids[0] + txids[1]) == headers[1][36:68]
    bits = []
    for i, header in enumerate(headers):
        height = 169 + i
        metadata = json.loads((SOURCE / ("mainnet-" + str(height) + ".json")).read_text())
        assert sha256d(header)[::-1].hex() == metadata["id"]
        if i:
            assert header[4:36] == sha256d(headers[i - 1])
        bits.append(int.from_bytes(header[72:76], "little"))
    assert bits == [0x1d00ffff] * 3
    target = 0xffff << (8 * (0x1d - 3))
    assert all(int.from_bytes(sha256d(header), "little") <= target for header in headers)
    payment = transactions[1]
    assert payment["version"] == 1 and payment["lock"] == 0 and len(payment["inputs"]) == 1 and len(payment["outputs"]) == 2
    assert payment["inputs"][0]["sequence"] == 0xffffffff and len(payment["inputs"][0]["script"]) <= 511
    assert all(len(o["script"]) == 67 and o["script"][:2] == b"\x41\x04" and o["script"][-1:] == b"\xac" for o in payment["outputs"])
    fixture = {"header" + str(i): header.hex() for i, header in enumerate(headers)}
    fixture.update(coinbase_txid_raw=txids[0].hex(), payment_txid_raw=txids[1].hex(), payment_raw=payment["raw"].hex(),
                   previous_hash_raw=payment["inputs"][0]["previous_hash"].hex(),
                   previous_index=str(payment["inputs"][0]["previous_index"]), script_sig=payment["inputs"][0]["script"].hex())
    for i, out in enumerate(payment["outputs"]):
        fixture.update({"value" + str(i): str(out["value"]), "key" + str(i) + "x": out["script"][2:34].hex(), "key" + str(i) + "y": out["script"][34:66].hex()})
    (DEST / "spv-receipt-fixture.tsv").write_text("field\tvalue\n" + "".join(key + "\t" + value + "\n" for key, value in fixture.items()))
    paths = [SOURCE / "mainnet-170.block"] + [SOURCE / ("mainnet-" + str(h) + suffix) for h in [169, 170, 171] for suffix in [".header.hex", ".json"]]
    sources = [dict(path=str(p.relative_to(ROOT)), sha256=hashlib.sha256(p.read_bytes()).hexdigest(), bytes=p.stat().st_size) for p in paths]
    (DEST / "spv-receipt-coverage.json").write_text(json.dumps(dict(sources=sources, block=170, transactions_parsed=2,
        block_bytes_consumed=pos, payment_bytes=len(payment["raw"]), headers=3, checkpoint=169, trusted_tip=171,
        fixed_epoch_bits="1d00ffff", target=hex(target), chainwork_for_3_headers=3 * ((1 << 256) // (target + 1)),
        target_payment_satoshis=payment["outputs"][0]["value"],
        assumption="Trusted best-chain checkpoint/tip and full Bitcoin consensus validation outside predicate; proof does not establish global fork choice"), indent=2) + "\n")
    print("Parsed all 2 transactions / 490 block bytes; verified 3 real PoW headers, links, receipt Merkle root and output serialization")


if __name__ == "__main__":
    main()
