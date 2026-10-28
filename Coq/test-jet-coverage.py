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
    import re
    signature = "bool simplicity_example(frameItem * dst, frameItem src, const txEnv * env);"
    assert coverage.declarations(f"/* {signature} */\n// {signature}\n{signature}") == ["simplicity_example"]
    rejects(lambda: coverage.declarations("bool simplicity_bad(int x);"), "signature")
    rows = coverage.inventory()
    # Even with a theorem registered for every other row, an input-restricted
    # mismatch theorem must not make the all-input completion gate succeed.
    complete = {"proof": "C.example.whole_jet", "condition": ""}
    mismatch = {"proof": "C.example.off_mismatch", "condition": "reported_mismatch"}
    absent = {"proof": "", "condition": ""}
    assert coverage.missing_equivalences([complete]) == []
    assert coverage.missing_equivalences([complete, mismatch]) == [mismatch]
    assert coverage.missing_equivalences([complete, absent, mismatch]) == [absent, mismatch]
    assert any(row["condition"] == "reported_mismatch" for row in coverage.missing_equivalences(rows))
    divergent = {**mismatch, "divergence_proof": "C.example.whole_jet_refutation"}
    assert coverage.missing_proofs([complete, mismatch]) == [mismatch]
    assert coverage.missing_proofs([complete, absent, divergent]) == [absent]
    assert coverage.missing_equivalences([complete, divergent]) == [divergent]
    assert sum(bool(row["divergence_proof"]) for row in rows) == 1
    assert len(coverage.missing_equivalences(rows)) == 12
    assert len(coverage.missing_proofs(rows)) == 11
    assert coverage.proof_roots(rows, ["simplicity_gej_ge_add_ex"]) == {
        "C.jet_secp_mixed_ex_local", "C.jet_secp_mixed_ex_refutation"}
    assert coverage.proof_roots(rows, ["simplicity_scale"]) == {"C.jet_secp_checked_scale_local"}
    rejects(lambda: coverage.proof_roots(rows, ["simplicity_off_curve_linear_combination_1"]),
            "jets without registered proof entries")
    rejects(lambda: coverage.proof_roots(rows, ["simplicity_not_a_jet"]),
            "jets without registered proof entries")
    # Computing indexed hashes and the Elements taproot builders retain
    # the explicit memcpy premise, including both Bitcoin value/script hashes.
    assert sum(row["condition"] == "memcpy_model" for row in rows) == 138
    # CTZ-dependent secp callers retain the explicit approved ctz premise.
    assert {row["function"] for row in rows if row["condition"] == "ctz_model"} == set(coverage._CTZ_JETS)
    assert {row["function"] for row in rows if row["condition"] == "memset_model"} == (
        set(coverage._MEMSET_JETS) | set(coverage._MEMSET_PARTIAL_JETS))
    expected = {name for header in coverage.HEADERS.values()
                for name in coverage.declarations((coverage.REPO / header).read_text())}
    assert {row["function"] for row in rows} == expected
    with tempfile.TemporaryDirectory(prefix="jet-coverage-tests.") as work:
        project = Path(work)
        (project / "C").mkdir()
        for name in ("jet_coverage.tsv", "jet_public_theorems.txt", "JET_SECP_RATIO_MISMATCHES.md"):
            shutil.copy2(SOURCE / "C" / name, project / "C" / name)
        shutil.copy2(SOURCE / "scan-jet-proofs.py", project / "scan-jet-proofs.py")
        for _, module, _ in coverage.records(SOURCE / "C/jet_coverage.tsv", 3):
            path = Path(module.replace(".", "/") + ".v")
            shutil.copy2(SOURCE / path, project / path)
        for entry in coverage.DIVERGENCE_CONTRACTS.values():
            path = Path(entry["module"].replace(".", "/") + ".v")
            shutil.copy2(SOURCE / path, project / path)
        coverage.COQ = project
        manifest = project / "C/jet_coverage.tsv"
        original = manifest.read_text()
        assert coverage.inventory() == rows
        # A report, restricted theorem, conditional negation, wrong target or
        # unaudited theorem cannot stand in for a whole-public refutation.
        for entry in coverage.DIVERGENCE_CONTRACTS.values():
            module, theorem = entry["module"], entry["theorem"]
            target = project / (module.replace(".", "/") + ".v")
            intact = target.read_text()
            declaration = "Theorem " + theorem + " :"
            for old, new in ((declaration, declaration + " False ->"),
                             ("~secp_jet_local_spec", "secp_jet_local_spec"),
                             ("f_simplicity_gej_ge_add_ex", "f_simplicity_gej_ge_add"),
                             ("@literal_gej_ge_add_ex", "@literal_gej_ge_add")):
                assert old in intact
                target.write_text(intact.replace(old, new, 1))
                rejects(coverage.inventory, "not the exact whole-jet refutation")
            target.write_text(intact)
            audited = project / "C/jet_public_theorems.txt"
            listed = audited.read_text()
            audited.write_text(listed.replace(f"{module} {theorem}\n", "", 1))
            rejects(coverage.inventory, "divergence theorem not publicly audited")
            audited.write_text(listed)
            report = project / entry["report"]
            text = report.read_text()
            report.write_text(text.replace(f"{module}.{theorem}", "removed"))
            rejects(coverage.inventory, "divergence proof not documented")
            report.write_text(text)
        assert coverage.inventory() == rows
        # Recovered proofs keep their exact complete public boundary. These
        # mutations test bookkeeping only; real sources still require Coq.
        for function in coverage.RECOVERED_CONTRACTS:
            row = next(r for r in rows if r["function"] == function)
            if not row["proof"]:
                continue  # A future batch has not registered this approved boundary yet.
            module, theorem = row["proof"].rsplit(".", 1)
            target = project / (module.replace(".", "/") + ".v")
            intact = target.read_text()
            declaration = "Theorem " + theorem + " :"
            start = intact.index(declaration)
            prefix, tail = intact[:start], intact[start:]
            variants = [tail.replace("f_" + function, "f_simplicity_verify", 1),
                        tail.replace(declaration, declaration + " False ->", 1),
                        tail.replace(".\nProof.", " -> True.\nProof.", 1)]
            if "memcpy_model ->" in tail:
                variants += [tail.replace("memcpy_model ->", "different_library_model ->", 1),
                             tail.replace("memcpy_model ->", "", 1)]
            if "ctz_model ->" in tail:
                variants += [tail.replace("ctz_model ->", "memset_model ->", 1),
                             tail.replace("ctz_model ->", "", 1),
                             tail.replace("ctz_model ->", "ctz_model -> ctz_model ->", 1)]
                for state in ("modinfo_fe_state", "modinfo_scalar_initialized", "swu_startup", "generator_startup"):
                    if state in tail:
                        variants.append(tail.replace(state, "(fun _ => True)", 1))
            if "memset_model ->" in tail:
                variants += [tail.replace("memset_model ->", "ctz_model ->", 1),
                             tail.replace("memset_model ->", "", 1)]
                for state in ("generator_startup", "scale_startup", "checked_scale_startup"):
                    if re.search(r"\b" + state + r"\b", tail):
                        variants.append(re.sub(r"\b" + state + r"\b", "(fun _ => True)", tail, count=1))
            if "secp_jet_initialized_partial_local_spec" in tail:
                variants.append(tail.replace("secp_jet_initialized_partial_local_spec",
                                             "secp_jet_initialized_local_spec", 1))
            if "beta_initialized" in tail:
                variants.append(tail.replace("beta_initialized", "(fun _ => True)", 1))
            for changed in variants:
                assert changed != tail
                target.write_text(prefix + changed)
                rejects(coverage.inventory, "not a direct canonical jet theorem")
            target.write_text(intact)
        assert coverage.inventory() == rows
        # A reported-mismatch entry keeps the unchanged literal target, the
        # exact excluded set, its whole-domain evidence and its report.
        for function, entry in coverage.REPORTED_MISMATCH_CONTRACTS.items():
            row = next(r for r in rows if r["function"] == function)
            assert row["condition"] == "reported_mismatch"
            module, theorem = row["proof"].rsplit(".", 1)
            target = project / (module.replace(".", "/") + ".v")
            intact = target.read_text()
            for old, new, message in (
                    ("(fun a=>~gej_ge_add_ex_ratio_mismatch a)", "(fun a=>True)", "not a direct canonical jet theorem"),
                    ("(fun a=>~gej_ge_add_ex_ratio_mismatch a)", "(fun a=>False)", "not a direct canonical jet theorem"),
                    ("f_simplicity_gej_ge_add_ex\n    gej_ge_add_ex_literal.",
                     "f_simplicity_gej_ge_add\n    gej_ge_add_ex_literal.", "not a direct canonical jet theorem"),
                    ("@literal_gej_ge_add_ex Alg.CoreFunSem a.", "@literal_gej_ge_add Alg.CoreFunSem a.",
                     "reported-mismatch definition changed"),
                    ("feP <= @toZ", "0 <= @toZ", "reported-mismatch definition changed")):
                assert old in intact, old
                target.write_text(intact.replace(old, new, 1))
                rejects(coverage.inventory, message)
            target.write_text(intact)
            report = project / entry["report"]
            text = report.read_text()
            for removed in (row["proof"],) + tuple(f"{module}.{t}" for t in entry["evidence"]):
                report.write_text(text.replace(removed, "removed"))
                rejects(coverage.inventory, "not documented")
            report.unlink()
            rejects(coverage.inventory, "not documented")
            report.write_text(text)
            audited = project / "C/jet_public_theorems.txt"
            listed = audited.read_text()
            audited.write_text(listed.replace(f"{module} {entry['evidence'][0]}\n", "", 1))
            rejects(coverage.inventory, "evidence not publicly audited")
            audited.write_text(listed)
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
        # The two field predicates use the same complete public contract.
        # Reject a helper, the wrong public function, a different contract,
        # and vacuous extra premises independently for each registration.
        for suffix in ("odd", "zero"):
            predicate = project / f"C/jet_secp_{suffix}_local.v"
            predicate_original = predicate.read_text()
            declaration = f"Theorem fe_{suffix}_local_spec :"
            contract = f"secp_jet_local_spec f_simplicity_fe_is_{suffix}"
            for old, new in (
                (contract, "secp_jet_local_spec f_read_fe"),
                (contract, "secp_jet_local_spec f_simplicity_fe_normalize"),
                (contract, f"jet_local_spec f_simplicity_fe_is_{suffix}"),
                (declaration, declaration + " False ->"),
            ):
                start = predicate_original.index(declaration)
                assert old in predicate_original[start:]
                predicate.write_text(predicate_original[:start] +
                                     predicate_original[start:].replace(old, new, 1))
                rejects(coverage.inventory, "not a direct canonical jet theorem")
            predicate.write_text(predicate_original)
        assert coverage.inventory() == rows
        # All point jets retain their own original function and whole contract.
        for filename, theorem, function in (
            ("jet_secp_gej_infinity_local.v", "gej_infinity_literal_local_spec", "simplicity_gej_infinity"),
            ("jet_secp_gej_predicate_local.v", "gej_is_infinity_literal_local_spec", "simplicity_gej_is_infinity"),
            ("jet_secp_gej_negate_local.v", "gej_negate_literal_local_spec", "simplicity_gej_negate"),
            ("jet_secp_ge_negate_local.v", "ge_negate_literal_local_spec", "simplicity_ge_negate"),
            ("jet_secp_curve_local.v", "ge_is_on_curve_literal_local_spec", "simplicity_ge_is_on_curve"),
            ("jet_secp_gej_curve_local.v", "gej_is_on_curve_literal_local_spec", "simplicity_gej_is_on_curve"),
            ("jet_secp_double_local.v", "gej_double_literal_local_spec", "simplicity_gej_double"),
            ("jet_secp_mixed_local.v", "gej_ge_add_literal_local_spec", "simplicity_gej_ge_add"),
            ("jet_secp_gej_add_local.v", "gej_add_literal_local_spec", "simplicity_gej_add"),
            ("jet_secp_gej_ge_equiv_local.v", "gej_ge_equiv_literal_local_spec", "simplicity_gej_ge_equiv"),
            ("jet_secp_gej_equiv_local.v", "gej_equiv_literal_local_spec", "simplicity_gej_equiv"),
            ("jet_secp_root_local.v", "fe_square_root_literal_local_spec", "simplicity_fe_square_root"),
            ("jet_secp_decompress_local.v", "decompress_literal_local_spec", "simplicity_decompress"),
            ("jet_secp_x_equiv_local.v", "gej_x_equiv_literal_local_spec", "simplicity_gej_x_equiv"),
            ("jet_secp_scalar_zero_local.v", "scalar_zero_local_spec", "simplicity_scalar_is_zero"),
            ("jet_secp_scalar_normalize_local.v", "scalar_normalize_local_spec", "simplicity_scalar_normalize"),
            ("jet_secp_scalar_negate_local.v", "scalar_negate_local_spec", "simplicity_scalar_negate"),
            ("jet_secp_scalar_add_local.v", "scalar_add_literal_local_spec", "simplicity_scalar_add"),
            ("jet_secp_scalar_multiply_local.v", "scalar_multiply_literal_local_spec", "simplicity_scalar_multiply"),
            ("jet_secp_scalar_square_local.v", "scalar_square_literal_local_spec", "simplicity_scalar_square"),
        ):
            point = project / ("C/" + filename)
            point_original = point.read_text()
            declaration = "Theorem " + theorem + " :"
            contract = "secp_jet_local_spec f_" + function
            for old, new in (
                (contract, "secp_jet_local_spec f_read_gej"),
                (contract, "secp_jet_local_spec f_simplicity_fe_add"),
                (contract, "jet_local_spec f_" + function),
                (declaration, declaration + " False ->"),
            ):
                start = point_original.index(declaration)
                assert old in point_original[start:]
                point.write_text(point_original[:start] + point_original[start:].replace(old, new, 1))
                rejects(coverage.inventory, "not a direct canonical jet theorem")
            point.write_text(point_original)
            assert coverage.inventory() == rows
        # Assertion jets must retain the exact linked program/environment and
        negate = project / "C/jet_secp_negate_literal_contract.v"
        negate_original = negate.read_text()
        declaration = "Theorem fe_negate_literal_local_spec :"
        contract = "secp_jet_local_spec f_simplicity_fe_negate"
        for old, new in (
            (contract, "secp_jet_local_spec f_read_fe"),
            (contract, "secp_jet_local_spec f_simplicity_fe_normalize"),
            (contract, "jet_local_spec f_simplicity_fe_negate"),
            (declaration, declaration + " False ->"),
        ):
            start = negate_original.index(declaration)
            assert old in negate_original[start:]
            negate.write_text(negate_original[:start] +
                              negate_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        negate.write_text(negate_original)
        assert coverage.inventory() == rows
        # Field addition must retain its own original function and whole contract.
        add = project / "C/jet_secp_add_local.v"
        add_original = add.read_text()
        declaration = "Theorem fe_add_literal_local_spec :"
        contract = "secp_jet_local_spec f_simplicity_fe_add"
        for old, new in (
            (contract, "secp_jet_local_spec f_read_fe"),
            (contract, "secp_jet_local_spec f_simplicity_fe_negate"),
            (contract, "jet_local_spec f_simplicity_fe_add"),
            (declaration, declaration + " False ->"),
        ):
            start = add_original.index(declaration)
            assert old in add_original[start:]
            add.write_text(add_original[:start] +
                           add_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        add.write_text(add_original)
        assert coverage.inventory() == rows
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
        # Elements currently admits only the reviewed Version boundary. This
        # fixture checks metadata, not proof validity; the source-identity gate
        # separately checks the literal target and the exact representation.
        elements = project / "C/jet_elements_version_local.v"
        shutil.copy2(SOURCE / "C/jet_elements_version_local.v", elements)
        elements_original = elements.read_text()
        elements_row = "simplicity_version C.jet_elements_version_local elements_version_local_spec\n"
        if not any(row["function"] == "simplicity_version" and row["proof"] for row in application_inventory):
            manifest.write_text(application_rows + elements_row)
        if ["C.jet_elements_version_local", "elements_version_local_spec"] not in coverage.records(audited, 2):
            audited.write_text(audited.read_text() + "C.jet_elements_version_local elements_version_local_spec\n")
        elements_inventory = coverage.inventory()
        for old, new in (
            ("f_simplicity_version elements_ge", "f_simplicity_lock_time elements_ge"),
            ("elements_ge Elements.env", "ge0 Elements.env"),
            ("elements_ge Elements.env", "elements_ge Bitcoin.env"),
            ("Elements.env Ty.Unit Word32", "Elements.env Ty.Unit Word64"),
            ("Theorem elements_version_local_spec :", "Theorem elements_version_local_spec : False ->"),
        ):
            assert old in elements_original
            elements.write_text(elements_original.replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        elements.write_text(elements_original)
        assert coverage.inventory() == elements_inventory
        for suffix, function in [('locktime', 'lock_time'), ('current_index', 'current_index')]:
            module = 'C.jet_elements_' + suffix + '_local'
            theorem = 'elements_' + suffix + '_local_spec'
            file = project / ('C/jet_elements_' + suffix + '_local.v')
            shutil.copy2(SOURCE / file.relative_to(project), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + function and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + function + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            for old, new in [('f_simplicity_' + function + ' elements_ge', 'f_simplicity_version elements_ge'),
                             ('elements_ge Elements.env', 'ge0 Elements.env'),
                             ('Elements.env Ty.Unit Word32', 'Elements.env Ty.Unit Word64'),
                             ('Theorem ' + theorem + ' :', 'Theorem ' + theorem + ' : False ->')]:
                file.write_text(text.replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
        # Count contracts retain the exact function, linked environment, width
        # and entire proposition. The separate source gate pins their literal
        # firstFail specification and initial environment relation.
        for suffix in ['num_inputs', 'num_outputs']:
            module = 'C.jet_elements_count_local'
            theorem = 'elements_' + suffix + '_local_spec'
            file = project / 'C/jet_elements_count_local.v'
            shutil.copy2(SOURCE / 'C/jet_elements_count_local.v', file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                ('Elements.env Ty.Unit Word32', 'Elements.env Ty.Unit Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Sequence contracts have different frame/input/output shapes. Test
        # each whole proposition, never compiled fake proofs.
        for suffix, module, contract in [
            ('input_sequence', 'C.jet_elements_indexed_scalar_jets', 'application_jet_local_spec_sep'),
            ('current_sequence', 'C.jet_elements_current_jets', 'application_jet_local_spec'),
        ]:
            theorem = 'elements_' + suffix + '_local_spec'
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                ('Elements.env ' + ('Word32' if suffix == 'input_sequence' else 'Ty.Unit Word32'),
                 'Elements.env ' + ('Word64' if suffix == 'input_sequence' else 'Ty.Unit Word64')),
                (declaration, declaration + ' False ->'),
                (contract + ' f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Direct getters retain exact separated contracts, widths, linked
        # and logical environments. Never compile these corrupted fixtures.
        for suffix, filename, width in [
            ('tapleaf_version', 'tapleaf_version', 'Word8'),
            ('script_cmr', 'script_cmr', 'Word256'),
            ('genesis_block_hash', 'genesis_hash', 'Word256'),
        ]:
            module = 'C.jet_elements_' + filename + '_local'
            theorem = 'elements_' + suffix + '_local_spec'
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (width, 'Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                assert old in text[start:]
                file.write_text(text[:start] + text[start:].replace(old, new, 1))
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Seven whole-C contracts, including both failure-return contracts
        # and both pegin tags. These corrupted fixtures are never compiled.
        for suffix, filename, theorem, domain, output, contract in [
            ('tx_is_final', 'is_final_local', 'elements_tx_is_final_local_spec', 'Ty.Unit', 'Bit', 'application_jet_local_spec_sep'),
            ('tx_lock_height', 'lock_local', 'elements_tx_lock_height_local_spec', 'Ty.Unit', 'Word32', 'application_jet_local_spec_sep'),
            ('tx_lock_time', 'lock_local', 'elements_tx_lock_time_local_spec', 'Ty.Unit', 'Word32', 'application_jet_local_spec_sep'),
            ('check_lock_height', 'check_lock', 'elements_check_lock_height_local_spec', '(Word 5)', 'Ty.Unit', 'application_jet_partial_spec'),
            ('check_lock_time', 'check_lock', 'elements_check_lock_time_local_spec', '(Word 5)', 'Ty.Unit', 'application_jet_partial_spec'),
            ('input_pegin', 'pegin_local', 'elements_input_pegin_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))', 'application_jet_local_spec_sep'),
            ('current_pegin', 'current_gen_jets', 'elements_current_pegin_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)', 'application_jet_local_spec_sep'),
        ]:
            module = 'C.jet_elements_' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                (contract + ' f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                # Normalize whitespace only to locate the exact type fragment.
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Eight exact indexed/current digest contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('input_script_hash', 'jet_elements_input_hash_jets', 'elements_input_script_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('input_script_sig_hash', 'jet_elements_input_hash_jets', 'elements_input_script_sig_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('current_script_hash', 'jet_elements_current_input_jets', 'elements_current_script_hash_local_spec', 'Ty.Unit', 'Word256'), ('current_script_sig_hash', 'jet_elements_current_input_jets', 'elements_current_script_sig_hash_local_spec', 'Ty.Unit', 'Word256'), ('issuance_asset_proof', 'jet_elements_input_hash_jets', 'elements_issuance_asset_proof_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('issuance_token_proof', 'jet_elements_input_hash_jets', 'elements_issuance_token_proof_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('current_issuance_asset_proof', 'jet_elements_current_input_jets', 'elements_current_issuance_asset_proof_local_spec', 'Ty.Unit', 'Word256'), ('current_issuance_token_proof', 'jet_elements_current_input_jets', 'elements_current_issuance_token_proof_local_spec', 'Ty.Unit', 'Word256')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Thirteen optional/outpoint/output contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('input_annex_hash', 'jet_elements_annex_local', 'elements_input_annex_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'), ('current_annex_hash', 'jet_elements_current_gen_jets', 'elements_current_annex_hash_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)'), ('reissuance_blinding', 'jet_elements_issuance_jets', 'elements_reissuance_blinding_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'), ('current_reissuance_blinding', 'jet_elements_current_input_jets', 'elements_current_reissuance_blinding_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)'), ('new_issuance_contract', 'jet_elements_issuance_jets', 'elements_new_issuance_contract_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'), ('current_new_issuance_contract', 'jet_elements_current_input_jets', 'elements_current_new_issuance_contract_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)'), ('reissuance_entropy', 'jet_elements_issuance_jets', 'elements_reissuance_entropy_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'), ('current_reissuance_entropy', 'jet_elements_current_input_jets', 'elements_current_reissuance_entropy_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit Word256)'), ('input_prev_outpoint', 'jet_elements_indexed_ptr_jets', 'elements_input_prev_outpoint_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))'), ('current_prev_outpoint', 'jet_elements_current_input_jets', 'elements_current_prev_outpoint_local_spec', 'Ty.Unit', '(Ty.Prod Word256 Word32)'), ('output_script_hash', 'jet_elements_indexed_ptr_jets', 'elements_output_script_hash_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('output_surjection_proof', 'jet_elements_output_proof_jets', 'elements_output_surjection_proof_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)'), ('output_range_proof', 'jet_elements_output_proof_jets', 'elements_output_range_proof_local_spec', 'Word32', '(Ty.Sum Ty.Unit Word256)')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Two raw-key/byte-index contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('internal_key', 'jet_elements_hash_field_jets', 'elements_internal_key_local_spec', 'Ty.Unit', 'Word256'), ('tappath', 'jet_elements_tappath_nullable', 'elements_tappath_u8_local_spec', 'Word8', '(Ty.Sum Ty.Unit Word256)')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Exact original C lbtc asset contract; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('lbtc_asset', 'jet_elements_lbtc_asset_local', 'elements_lbtc_asset_local_spec', 'Ty.Unit', 'Word256')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word16'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Historical relative-lock whole-C contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('broken_do_not_use_tx_lock_distance', 'jet_elements_legacy_lock_local', 'elements_broken_tx_lock_distance_local_spec', 'Ty.Unit', 'Word16'), ('broken_do_not_use_tx_lock_duration', 'jet_elements_legacy_lock_local', 'elements_broken_tx_lock_duration_local_spec', 'Ty.Unit', 'Word16')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Historical relative-lock assertions; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('broken_do_not_use_check_lock_distance', 'jet_elements_legacy_check', 'elements_broken_check_lock_distance_local_spec', 'Word16', 'Ty.Unit'), ('broken_do_not_use_check_lock_duration', 'jet_elements_legacy_check', 'elements_broken_check_lock_duration_local_spec', 'Word16', 'Ty.Unit')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_partial_spec f_simplicity_' + suffix, 'application_jet_local_spec_sep f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal optional nonce whole-C contract; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('output_nonce', 'jet_elements_output_nonce_literal', 'elements_output_nonce_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfNonce))')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal asset getter whole-C contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('input_asset', 'jet_elements_asset_literal', 'elements_input_asset_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit AssetConf)'), ('output_asset', 'jet_elements_asset_literal', 'elements_output_asset_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit AssetConf)'), ('current_asset', 'jet_elements_asset_literal', 'elements_current_asset_literal_local_spec', 'Ty.Unit', 'AssetConf')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal amount getter whole-C contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('input_amount', 'jet_elements_amount_literal', 'elements_input_amount_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit AmountPair)'), ('output_amount', 'jet_elements_amount_literal', 'elements_output_amount_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit AmountPair)'), ('current_amount', 'jet_elements_amount_literal', 'elements_current_amount_literal_local_spec', 'Ty.Unit', 'AmountPair')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal issuance asset-amount whole-C contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('issuance_asset_amount', 'jet_elements_issuance_amount_literal', 'elements_issuance_asset_amount_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfAmount))'), ('current_issuance_asset_amount', 'jet_elements_issuance_amount_literal', 'elements_current_issuance_asset_amount_literal_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit ConfAmount)')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal issuance token-amount whole-C contracts; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('issuance_token_amount', 'jet_elements_token_amount_literal', 'elements_issuance_token_amount_literal_local_spec', 'Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfAmount))'), ('current_issuance_token_amount', 'jet_elements_token_amount_literal', 'elements_current_issuance_token_amount_literal_local_spec', 'Ty.Unit', '(Ty.Sum Ty.Unit ConfAmount)')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Literal transaction_id whole-C contract; never compile bad fixtures.
        for suffix, filename, theorem, domain, output in [('transaction_id', 'jet_elements_transaction_id_literal', 'elements_transaction_id_literal_local_spec', 'Ty.Unit', 'Word256')]:
            module = 'C.' + filename
            file = project / (module.replace('.', '/') + '.v')
            shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
            text = file.read_text()
            if not any(r['function'] == 'simplicity_' + suffix and r['proof'] for r in coverage.inventory()):
                manifest.write_text(manifest.read_text() + 'simplicity_' + suffix + ' ' + module + ' ' + theorem + '\n')
            if [module, theorem] not in coverage.records(audited, 2):
                audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
            declaration = 'Theorem ' + theorem + ' :'
            for old, new in [
                ('f_simplicity_' + suffix + ' elements_ge', 'f_simplicity_version elements_ge'),
                ('elements_ge Elements.env', 'ge0 Elements.env'),
                ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                (domain + ' ' + output, 'Word64 ' + output),
                (domain + ' ' + output, domain + ' Word64'),
                (declaration, declaration + ' False ->'),
                ('application_jet_local_spec_sep f_simplicity_' + suffix, 'application_jet_local_spec f_simplicity_' + suffix),
            ]:
                start = text.index(declaration)
                stop = text.index('Proof.', start)
                tail = text[start:stop]
                if old not in tail:
                    import re
                    match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                    assert match, (suffix, old)
                    old = match[0]
                file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
                rejects(coverage.inventory, 'not a direct canonical jet theorem')
            file.write_text(text)
            assert coverage.inventory()
        # Explicit contextual family; do not accept a hidden precondition,
        # wrong spec/relation/width, or substitute the broader local API.
        module = 'C.jet_elements_null_data_literal'
        theorem = 'elements_output_null_datum_literal_bitmachine_spec'
        file = project / (module.replace('.', '/') + '.v')
        shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
        text = file.read_text()
        if not any(r['function'] == 'simplicity_output_null_datum' and r['proof'] for r in coverage.inventory()):
            manifest.write_text(manifest.read_text() + 'simplicity_output_null_datum ' + module + ' ' + theorem + '\n')
        if [module, theorem] not in coverage.records(audited, 2):
            audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
        declaration = 'Theorem ' + theorem + ' :'
        for old, new in [
            ('f_simplicity_output_null_datum', 'f_simplicity_output_script_hash'),
            ('elements_ge Elements.env', 'ge0 Elements.env'),
            ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
            ('(Ty.Prod Word32 Word32)', '(Ty.Prod Word64 Word32)'),
            ('ResultTy', 'Word256'),
            ('elements_null_data_environment_rep', '(fun _ _ _ _ => True)'),
            ('elements_output_null_datum_literal_spec', '(fun _ _ => Some (inl tt))'),
            (declaration, declaration + ' False ->'),
            ('application_jet_bitmachine_spec', 'application_jet_local_spec_sep'),
            ('elements_output_null_datum_literal_spec.', 'elements_output_null_datum_literal_spec -> True.'),
        ]:
            start = text.index(declaration)
            stop = text.index('Proof.', start)
            tail = text[start:stop]
            if old not in tail:
                import re
                match = re.search(r'\s+'.join(map(re.escape, old.split())), tail)
                assert match, old
                old = match[0]
            file.write_text(text[:start] + tail.replace(old, new, 1) + text[stop:])
            rejects(coverage.inventory, 'not a direct canonical jet theorem')
        file.write_text(text)
        assert coverage.inventory()
        # The initialized lambda theorem has an exact constant/function/term
        # boundary, not an arbitrary Ready alias or the unrestricted old API.
        module = 'C.jet_secp_scalar_lambda_local'
        theorem = 'scalar_lambda_initialized_local_spec'
        file = project / (module.replace('.', '/') + '.v')
        shutil.copy2(SOURCE / (module.replace('.', '/') + '.v'), file)
        text = file.read_text()
        if not any(r['function'] == 'simplicity_scalar_multiply_lambda' and r['proof'] for r in coverage.inventory()):
            manifest.write_text(manifest.read_text() + 'simplicity_scalar_multiply_lambda ' + module + ' ' + theorem + '\n')
        if [module, theorem] not in coverage.records(audited, 2):
            audited.write_text(audited.read_text() + module + ' ' + theorem + '\n')
        declaration = 'Theorem ' + theorem + ' :'
        for old, new in [
            ('secp_jet_initialized_local_spec scalar_lambda_initialized', 'secp_jet_initialized_local_spec True'),
            ('secp_jet_initialized_local_spec scalar_lambda_initialized', 'secp_jet_local_spec'),
            ('f_simplicity_scalar_multiply_lambda', 'f_simplicity_scalar_square'),
            ('(Word 8) (Word 8)', '(Word 9) (Word 8)'),
            ('(Word 8) (Word 8)', '(Word 8) (Word 9)'),
            ('@canonical_scalar_multiply_lambda', '@canonical_scalar_square'),
            ('Alg.CoreFunSem', 'wrong_algebra'),
            (declaration, declaration + ' False ->'),
            ('Alg.CoreFunSem).', 'Alg.CoreFunSem) -> True.'),
        ]:
            start = text.index(declaration)
            stop = text.index('Proof.', start)
            body = text[start:stop]
            assert old in body, old
            file.write_text(text[:start] + body.replace(old, new, 1) + text[stop:])
            rejects(coverage.inventory, 'not a direct canonical jet theorem')
        file.write_text(text)
        assert coverage.inventory()
    print("coverage tests passed: exact core/partial/application contracts; wrong function/global/logical environment and unknown/duplicate/helper/unaudited entries rejected")


if __name__ == "__main__":
    main()
