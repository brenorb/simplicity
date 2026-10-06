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
    assert sum(row["condition"] == "memcpy_model" for row in rows) == 104
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
        # Regression for a contract merely occurring inside a weaker/vacuous
        # proposition. These are metadata tests, not compiled fake proofs.
        direct = project / "C/jet_constant_layout.v"
        direct_original = direct.read_text()
        declaration = "Corollary low1_local_spec :"
        assert declaration in direct_original
        for prefix, suffix in (("False -> ", ""), ("", " -> True"),
                               ("", " \\/ True"), ("", " /\\ True")):
            direct.write_text(direct_original.replace(
                declaration, declaration + " " + prefix, 1))
            if suffix:
                text = direct.read_text()
                start = text.index(declaration)
                end = text.index(".\nProof.", start)
                direct.write_text(text[:end] + suffix + text[end:])
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        direct.write_text(direct_original)
        conditional_path = project / "C/jet_core_projection_jets.v"
        conditional_original = conditional_path.read_text()
        for old, new in (
            ("memcpy_model ->", "False -> memcpy_model ->"),
            ("memcpy_model ->", "another_library_model ->"),
            ("f_simplicity_leftmost_8_1", "f_simplicity_leftmost_8_2"),
        ):
            conditional_path.write_text(conditional_original.replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        conditional_path.write_text(conditional_original)
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
        # Free cached hashes are auxiliary until the raw canonical projection
        # is present; a cache-only environment cannot be registered as final.
        raw_jets = project / "C/jet_bitcoin_raw_jets.v"
        raw_original = raw_jets.read_text()
        raw_jets.write_text(raw_original.replace(
            "raw_bitcoin_environment Ty.Unit Word256", "ext_environment Ty.Unit Word256", 1))
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        raw_jets.write_text(raw_original)
        # The secp contract is counted only for the reviewed public function
        # and only as the entire proposition. Its linked environment and
        # literal canonical program are checked by the specification gate.
        secp = project / "C/jet_secp_normalize_local.v"
        secp_original = secp.read_text()
        declaration = "Theorem fe_normalize_local_spec :"
        for old, new in (
            ("secp_jet_local_spec f_simplicity_fe_normalize",
             "secp_jet_local_spec f_read_fe"),
            ("secp_jet_local_spec f_simplicity_fe_normalize",
             "jet_local_spec f_simplicity_fe_normalize"),
            (declaration, declaration + " False ->"),
        ):
            start = secp_original.index(declaration)
            secp.write_text(secp_original[:start] + secp_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        secp.write_text(secp_original)
        # Assertion jets must retain the exact linked program/environment and
        # be the whole proposition, including both success and failure.
        assertion = project / "C/jet_bitcoin_check_lock.v"
        assertion_original = assertion.read_text()
        for old, new in (
            ("application_jet_partial_spec f_simplicity_bitcoin_check_lock_height",
             "application_jet_partial_spec f_simplicity_bitcoin_check_lock_time"),
            ("bitcoin_ge Bitcoin.env", "ge0 Bitcoin.env"),
            ("bitcoin_ge Bitcoin.env", "bitcoin_ge ext_environment"),
            ("Theorem bitcoin_check_lock_height_local_spec :",
             "Theorem bitcoin_check_lock_height_local_spec : False ->"),
        ):
            assert old in assertion_original
            declaration_start = assertion_original.index("Theorem bitcoin_check_lock_height_local_spec")
            assertion.write_text(assertion_original[:declaration_start] +
                                 assertion_original[declaration_start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        assertion.write_text(assertion_original)
        # This positive fixture checks bookkeeping only. The actual application
        # theorem still requires compilation, kernel and assumption gates.
        application_name = "simplicity_bitcoin_version"
        application_module = "C.jet_bitcoin_version_local"
        application_theorem = "bitcoin_version_local_spec"
        application = project / "C/jet_bitcoin_version_local.v"
        shutil.copy2(SOURCE / "C/jet_bitcoin_version_local.v", application)
        application_original = application.read_text()
        application_rows = original
        if not any(row["function"] == application_name and row["proof"] for row in rows):
            application_rows += f"{application_name} {application_module} {application_theorem}\n"
        manifest.write_text(application_rows)
        audited = project / "C/jet_public_theorems.txt"
        audited_original = audited.read_text()
        if (application_module, application_theorem) not in coverage.records(audited, 2):
            audited.write_text(audited_original + f"{application_module} {application_theorem}\n")
        application_inventory = coverage.inventory()
        assert next(row for row in application_inventory if row["function"] == application_name)["proof"]
        for old, new in (
            ("application_jet_local_spec f_simplicity_bitcoin_version", "application_jet_local_spec f_simplicity_bitcoin_lock_time"),
            ("bitcoin_ge Bitcoin.env", "ge0 Bitcoin.env"),
            ("bitcoin_ge Bitcoin.env", "bitcoin_ge Elements.env"),
            ("application_jet_local_spec f_simplicity_bitcoin_version", "jet_local_spec f_simplicity_bitcoin_version"),
        ):
            assert old in application_original
            application.write_text(application_original.replace(old, new))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        application.write_text(application_original)
        assert coverage.inventory() == application_inventory
    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")


if __name__ == "__main__":
    main()
