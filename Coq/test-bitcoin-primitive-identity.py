#!/usr/bin/env python3
"""Regression checks for both Bitcoin signatures' canonical identities."""
import importlib.util
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("bitcoin_identity", ROOT / "check-bitcoin-primitive-identity.py")
identity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(identity)


def rejects(path, text, message):
    path.write_text(text)
    try:
        identity.check(base_model=path)
    except ValueError as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError(f"expected rejection: {message}")


def main():
    assert identity.check() == 8
    original = identity.BASE_MODEL.read_text()
    with tempfile.TemporaryDirectory(prefix="bitcoin-identity.") as work:
        base = Path(work) / "Bitcoin.v"
        rejects(base, original.replace('primName : string := "Bitcoin"',
                                       'primName : string := "BitcoinExt"'),
                "base primitive tag namespace differs")
        rejects(base, original.replace('| LockTime => "lockTime"', '| LockTime => "locktime"'),
                "base primitive name mismatch: LockTime")
        rejects(base, original.replace('| InputValue : prim Word32 (Sum Unit Word64)',
                                       '| InputValue : prim Word32 (Sum Unit Word32)'),
                "base primitive type mismatch: InputValue")
        rejects(base, original.replace('| ScriptCMR : prim Unit Word256.', '.'),
                "canonical primitive constructor coverage differs")
        base.write_text(original)
        assert identity.check(base_model=base) == 8
    print("Bitcoin identity tests passed: base namespace/names/types and missing canonical constructors rejected")


if __name__ == "__main__":
    main()
