#!/usr/bin/env python3
"""Project CAT steps from pinned script tests without running upstream code."""

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "vendor-specs/bip347-cat"
LIMIT = 520

# One-based JSON array positions, including its section headings.
SKIPPED = {
    705: "legacy disabled opcode",
    706: "legacy disabled opcode in untaken branch",
    1180: "section heading",
    1181: "OP_SUCCESS without CAT activation",
    1182: "discouraged by policy before evaluation",
    1183: "discouraged by policy before evaluation",
    1184: "discouraged by policy before evaluation",
    1185: "control script contains no CAT",
    1186: "discourage-policy precedence before evaluation",
    1187: "empty stack underflow",
    1188: "section heading",
    1189: "empty stack underflow",
    1192: "OP_SUCCESS without CAT activation",
    1201: "untaken CAT branch",
    1205: "empty stack underflow",
    1206: "single-element stack underflow",
}


def hash256(data):
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def explicit_push(script):
    match = re.search(r"0x4c 0x([0-9a-f]{2}) 0x([0-9a-f]+) EQUAL$", script)
    assert match is not None
    size, data = match.groups()
    result = bytes.fromhex(data)
    assert len(result) == int(size, 16)
    return result


def project_json(rows, relation):
    inventory = []
    for i in sorted(SKIPPED.keys() | set(range(1180, 1212))):
        row = rows[i - 1]
        if i in SKIPPED:
            inventory.append((i, 0, SKIPPED[i], row[-1]))
            continue
        witness, script_sig, script_pubkey, flags, expect, description = row
        assert script_sig == "" and script_pubkey == "0x51 0x20 #TAPROOTOUTPUT#"
        assert "OP_CAT" in flags.split(",") and witness[-2] == "#CONTROLBLOCK#"
        stack = [bytes.fromhex(item) for item in witness[:-3]]
        script = witness[-3].removeprefix("#SCRIPT# ")
        steps = []

        def emit(left, right, result=None):
            joined = left + right
            within_limit = len(joined) <= LIMIT
            claim = (joined if within_limit else b"") if result is None else result
            steps.append((left, right, claim, within_limit and joined == claim))
            return joined

        if script == "CAT":
            emit(*stack)
        elif script in ("CAT EQUAL", "CAT EQUALVERIFY"):
            emit(*stack[-2:], result=stack[-3])
        elif script.startswith("CAT 0x4c"):
            emit(*stack, result=explicit_push(script))
        elif script.startswith("CAT CAT DUP DROP "):
            tail = emit(*stack[-2:])
            emit(stack[0], tail, result=explicit_push(script))
        elif script == "IF CAT ELSE DROP ENDIF":
            assert stack.pop() == b"\x01"
            emit(*stack)
        elif script == " ".join(["DUP CAT"] * 7):
            value, = stack
            for _ in range(7):
                value = emit(value, value)
                if len(value) > LIMIT:
                    break
        else:
            assert script == "HASH256 DUP SHA1 CAT DUP CAT TOALTSTACK HASH256 DUP CAT TOALTSTACK FROMALTSTACK"
            a, b = stack
            hashed = hash256(b)
            first = emit(hashed, hashlib.sha1(hashed).digest())
            emit(first, first)
            second = hash256(a)
            emit(second, second)

        assert expect in ("OK", "PUSH_SIZE", "EQUALVERIFY", "EVAL_FALSE")
        assert all(s[-1] for s in steps) == (expect == "OK")
        assert expect != "PUSH_SIZE" or len(steps[-1][0] + steps[-1][1]) > LIMIT
        for j, step in enumerate(steps, 1):
            relation.append((f"PR29247 JSON row {i} step {j}", *step))
        inventory.append((i, len(steps), "typed CAT steps", description))
    return inventory


def project_cpp(source, relation):
    assert 'ParseHex("aa")' in source and 'ParseHex("bbbb")' in source
    assert '0x03, 0xaa, 0xbb, 0xbb, OP_EQUAL' in source
    assert "BOOST_AUTO_TEST_CASE(cat_empty_stack)" in source
    relation.append(("PR29247 C++ cat_simple", b"\xaa", b"\xbb\xbb", b"\xaa\xbb\xbb", True))
    relation.append(("PR29247 C++ cat_empty_stack", b"", b"", b"", True))
    start = source.index("BOOST_AUTO_TEST_CASE(cat_dup_test)")
    body = source[start:]
    assert "maxElementSize = 522" in body and "maxDupsToCheck = 10" in body
    assert "witData.at(0).emplace_back(0x1A);" in body
    assert re.search(r"expectedErr = SCRIPT_ERR_PUSH_SIZE;\s+break;", body)
    assert re.search(r"if \(expectedErr == SCRIPT_ERR_OK\)\s+break;", body)
    # The failure break occurs before DoTest. After success it breaks too.
    # Consequently the actual upstream native unit inputs cover one doubling
    # for lengths 1..260, with no DoTest call for sizes 261..522.
    for size in range(1, LIMIT // 2 + 1):
        value = b"\x1a" * size
        relation.append((f"PR29247 C++ cat_dup_test {size} bytes", value, value, value + value, True))


def tsv(header, rows):
    output = io.StringIO(newline="")
    writer = csv.writer(output, delimiter="\t", lineterminator="\n", quoting=csv.QUOTE_NONE)
    writer.writerow(header)
    writer.writerows(rows)
    return output.getvalue()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    script_tests = json.loads((PACKET / "upstream/script_tests.json").read_text())
    assert len(script_tests) == 1305
    spec = (ROOT / "vendor-specs/bip-inventory/upstream/bip-0347.mediawiki").read_text()
    inline = spec.split("==Test Vectors==", 1)[1].split("<pre>", 1)[1].split("</pre>", 1)[0].strip().rstrip(",")
    assert json.loads("[" + inline + "]") == [script_tests[i - 1] for i in (1191, 1200, 1207)]
    relation = []
    inventory = project_json(script_tests, relation)
    assert [i for i, row in enumerate(script_tests, 1) if "CAT" in json.dumps(row)] == [i for i, *_ in inventory]
    json_steps = len(relation)
    project_cpp((PACKET / "upstream/script_tests.cpp").read_text(), relation)
    assert len(relation) == json_steps + 262
    files = {
        "relation-vectors.tsv": tsv(
            ("name", "left_hex", "right_hex", "result_hex", "expected"),
            ((name, left.hex(), right.hex(), result.hex(), "accept" if ok else "reject")
             for name, left, right, result, ok in relation),
        ),
        "script-json-inventory.tsv": tsv(
            ("json_row", "cat_steps", "scope", "upstream_description"), inventory,
        ),
    }
    for name, data in files.items():
        path = PACKET / name
        if args.check:
            assert path.read_bytes() == data.encode(), f"changed generated vector file {name}"
        else:
            path.write_bytes(data.encode())
    print(f"{len(inventory)} CAT-related JSON rows, {json_steps} typed JSON steps, "
          f"262 actual C++ CAT unit inputs, {len(relation)} total upstream projections")


if __name__ == "__main__":
    main()
