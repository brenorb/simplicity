#!/usr/bin/env python3
"""Check that coverage bookkeeping cannot hide missing jets or count helpers."""
import importlib.util
import shutil
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("jet_coverage", SOURCE / "jet-coverage.py")
coverage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(coverage)


def rejects(action, message):
    try:
        action()
    except ValueError as error:
        assert message in str(error), str(error)
    else:
        raise AssertionError(f"expected rejection: {message}")


def main():
    signature = "bool simplicity_example(frameItem * dst, frameItem src, const txEnv * env);"
    assert coverage.declarations(f"/* {signature} */\n// {signature}\n{signature}") == ["simplicity_example"]
    rejects(lambda: coverage.declarations("bool simplicity_bad(int x);"), "signature")
    rows = coverage.inventory()
    expected = {name for header in coverage.HEADERS.values()
                for name in coverage.declarations((coverage.REPO / header).read_text())}
    assert {row["function"] for row in rows} == expected
    with tempfile.TemporaryDirectory(prefix="jet-coverage-tests.") as work:
        project = Path(work)
        (project / "C").mkdir()
        for name in ("jet_coverage.tsv", "jet_public_theorems.txt"):
            shutil.copy2(SOURCE / "C" / name, project / "C" / name)
        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")
        for _, module, _ in coverage.records(SOURCE / "C/jet_coverage.tsv", 3):
            path = Path(module.replace(".", "/") + ".v")
            shutil.copy2(SOURCE / path, project / path)
        coverage.COQ = project
        manifest = project / "C/jet_coverage.tsv"
        original = manifest.read_text()
        assert coverage.inventory() == rows
        for extra, message in (
            ("simplicity_nonexistent C.jet_canonical one8_local_spec\n", "unknown jet"),
            ("simplicity_one_8 C.jet_canonical one8_local_spec\n", "duplicate coverage"),
        ):
            manifest.write_text(original + extra)
            rejects(coverage.inventory, message)
        manifest.write_text(original.replace("C.jet_constant_layout low1_local_spec",
                                              "C.jet_constant_layout constant_local_spec"))
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        manifest.write_text(original.replace("C.jet_constant_layout low1_local_spec",
                                              "C.jet_constant_layout unaudited_theorem"))
        rejects(coverage.inventory, "not publicly audited")
        # Partial/assertion specs are accepted only as named, audited contracts
        # of the exact public function, not as stronger helper results.
        manifest.write_text(original.replace("C.jet_verify_layout verify_local_spec",
                                              "C.jet_verify_layout verify_silent_guarantees"))
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        manifest.write_text(original)
        partial = project / "C/jet_verify_layout.v"
        partial_original = partial.read_text()
        partial.write_text(partial_original.replace(
            "jet_partial_local_spec f_simplicity_verify",
            "jet_partial_local_spec f_simplicity_some_1"))
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        partial.write_text(partial_original)
        assert coverage.inventory() == rows
    print("coverage tests passed: complete header inventory; total/partial exact-function contracts; unknown/duplicate/helper/unaudited entries rejected")


if __name__ == "__main__":
    main()
