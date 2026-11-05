#!/usr/bin/env python3
"""Extract complete named KAT sets from inert vendored primary text.

No downloaded source code is evaluated. Fails closed on unexpected row counts,
widths or source formatting; LF TSV outputs preserve exact published bytes.
"""
import csv
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
DATA = ROOT / "vendor-specs/transport-crypto"


def write(name, header, rows):
    with (DATA / name).open("w", newline="") as output:
        writer = csv.writer(output, delimiter="\t", lineterminator="\n")
        writer.writerow(header)
        writer.writerows(rows)


def byte_rows(text):
    result = bytearray()
    for line in text.splitlines():
        tokens = line.split()
        if not tokens or not re.fullmatch(r"\d{3}", tokens[0]):
            continue
        for token in tokens[1:17]:
            if not re.fullmatch(r"[0-9a-fA-F]{2}", token):
                break
            result.append(int(token, 16))
    return bytes(result)


def plain_rows(text):
    rows = [line.split() for line in text.splitlines()]
    return bytes(int(token, 16) for row in rows
                 if row and all(re.fullmatch(r"[0-9a-fA-F]{2}", token) for token in row)
                 for token in row)


def main():
    source = (DATA / "siphash-vectors.h.txt").read_text()
    array = source.split("vectors_sip64[64][8] = {", 1)[1].split("};", 1)[0]
    values = [int(x, 16) for x in re.findall(r"0x([0-9a-fA-F]{2})", array)]
    assert len(values) == 512
    write("siphash24-vectors.tsv", ["length", "key_hex", "message_hex", "digest_le_hex"],
          [(n, bytes(range(16)).hex(), bytes(range(n)).hex(), bytes(values[n*8:n*8+8]).hex())
           for n in range(64)])

    rfc = (DATA / "rfc8439.txt").read_text()
    appendix = rfc.rsplit("A.1.  The ChaCha20 Block Functions", 1)[1].split("A.2.", 1)[0]
    cases = re.split(r"Test Vector #(\d+):", appendix)[1:]
    assert len(cases) == 10
    rows = []
    section = rfc.rsplit("2.3.2.  Test Vector for the ChaCha20 Block Function", 1)[1].split("2.4.", 1)[0]
    expected = byte_rows(section.split("Serialized Block:", 1)[1])
    assert len(expected) == 64
    # These key/nonce/counter bytes are explicitly printed in section2.3.2.
    rows.append(("2.3.2", bytes(range(32)).hex(), 1, "000000090000004a00000000", expected.hex()))
    for i in range(0, len(cases), 2):
        number, text = cases[i:i+2]
        key = byte_rows(text.split("Key:", 1)[1].split("Nonce:", 1)[0])
        nonce = byte_rows(text.split("Nonce:", 1)[1].split("Block Counter", 1)[0])
        counter = int(re.search(r"Block Counter = (\d+)", text)[1])
        result = byte_rows(text.split("Keystream:", 1)[1])
        assert (len(key), len(nonce), len(result)) == (32, 12, 64)
        rows.append(("A.1."+number, key.hex(), counter, nonce.hex(), result.hex()))
    assert len(rows) == 6
    write("chacha20-block-vectors.tsv", ["case", "key_hex", "counter", "nonce_hex", "block_hex"], rows)

    main_case = rfc.rsplit("2.5.2.  Poly1305 Example and Test Vector", 1)[1].split("2.6.", 1)[0]
    key_hex = re.sub(r"[\s:]", "", main_case.split("Key Material:", 1)[1].split("o  s as", 1)[0])
    assert re.fullmatch(r"[0-9a-fA-F]{64}", key_hex)
    message = byte_rows(main_case.split("Message to be Authenticated:", 1)[1].split("Since Poly1305", 1)[0])
    tag = bytes.fromhex(re.search(r"Tag: ([0-9a-f:]+)", main_case)[1].replace(":", ""))
    assert len(message) == 34 and len(tag) == 16
    rows = [("2.5.2", key_hex.lower(), message.hex(), tag.hex())]
    appendix = rfc.rsplit("A.3.  Poly1305 Message Authentication Code", 1)[1].split("A.4.", 1)[0]
    cases = re.split(r"Test Vector #(\d+):", appendix)[1:]
    assert len(cases) == 22
    for i in range(0, len(cases), 2):
        number, text = cases[i:i+2]
        if int(number) <= 4:
            key = byte_rows(text.split("One-time Poly1305 Key:", 1)[1].split("Text to MAC:", 1)[0])
            message = byte_rows(text.split("Text to MAC:", 1)[1].split("Tag:", 1)[0])
            tag = byte_rows(text.split("Tag:", 1)[1])
        else:
            key = plain_rows(text.split("R:", 1)[1].split("S:", 1)[0]) + plain_rows(text.split("S:", 1)[1].split("data:", 1)[0])
            message = plain_rows(text.split("data:", 1)[1].split("tag:", 1)[0])
            tag = plain_rows(text.split("tag:", 1)[1])
        assert len(key) == 32 and len(message) <= 511 and len(tag) == 16
        rows.append(("A.3."+number, key.hex(), message.hex(), tag.hex()))
    assert len(rows) == 12
    write("poly1305-vectors.tsv", ["case", "key_hex", "message_hex", "tag_le_hex"], rows)
    outputs = ["siphash24-vectors.tsv", "chacha20-block-vectors.tsv", "poly1305-vectors.tsv"]
    record = {"tool": "tools/extract_transport_vectors.py", "official_sets": {"siphash24": 64, "rfc8439_chacha20_block": 6, "rfc8439_poly1305": 12},
              "outputs": {name: hashlib.sha256((DATA/name).read_bytes()).hexdigest() for name in outputs}}
    (DATA / "derived-manifest.json").write_text(json.dumps(record, indent=2)+"\n")
    print("extracted all64 SipHash64, all6 RFC8439 complete-block and all12 Poly1305 KATs")


if __name__ == "__main__":
    main()
