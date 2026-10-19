#!/usr/bin/env python3
"""Regression checks: base-model mismatches must be documented, not corrected."""
import importlib.util
from pathlib import Path
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("bitcoin_identity", ROOT / "check-bitcoin-primitive-identity.py")
identity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(identity)


def rejects(message, base=None, report=None):
    try:
        identity.check_base(base_model=base or identity.BASE_MODEL,
                            report=report or identity.MISMATCH_REPORT)
    except ValueError as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError(f"expected rejection: {message}")


def main():
    assert identity.check() == 8
    assert identity.check_base() == [("name", "LockTime", "locktime", "lockTime")]
    model = identity.BASE_MODEL.read_text()
    report = identity.MISMATCH_REPORT.read_text()
    marker = '<!-- gate bitcoin-base name LockTime "locktime" "lockTime" -->'
    assert marker in report
    with tempfile.TemporaryDirectory(prefix="bitcoin-identity.") as work:
        base, doc = Path(work) / "Bitcoin.v", Path(work) / "report.md"
        doc.write_text(report.replace(marker, ""))
        rejects("undocumented base-model mismatch(es)", report=doc)
        doc.write_text(report)
        base.write_text(model.replace('| Version => "version"', '| Version => "Version"'))
        rejects("undocumented base-model mismatch(es)", base=base, report=doc)
        base.write_text(model.replace('| LockTime => "locktime"', '| LockTime => "lockTime"'))
        rejects("no longer present", base=base, report=doc)
        base.write_text(model.replace('primName : string := "Bitcoin"', 'primName : string := "BitcoinExt"'))
        rejects("namespace primName", base=base, report=doc)
    print("Bitcoin identity tests passed: undocumented, new and stale base-model mismatches rejected")


if __name__ == "__main__":
    main()
