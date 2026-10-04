#!/usr/bin/env python3
"""Negative tests for the review's gate bypasses, in an isolated built copy."""
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True


def run(args, cwd, succeeds=True):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if (result.returncode == 0) != succeeds:
        raise RuntimeError(f"unexpected result from {args}:\n{result.stdout}\n{result.stderr}")
    return result


def main():
    source = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix="jet-gate-tests.") as work:
        project = Path(work) / "Coq"
        # Preserve built dependencies; each changed fixture is compiled below.
        shutil.copytree(source, project, ignore=shutil.ignore_patterns(
            "__pycache__", "*Makefile*", ".lia.cache"))
        run(["bash", "audit-jet-contracts.sh"], project)
        # Use the real public guarantee as the fixture's proof term. Mutating
        # a shared module would rebuild hundreds of unrelated consumers and
        # could hit their bounded tactic timeouts before reaching the gate.
        # This dedicated public module has no consumers; every mutation is
        # compiled, with the same type and axioms as the real guarantee.
        fixture = project / "C/jet_gate_fixture.v"
        original = ("Require Import C.jet_guarantees.\n"
                    "Definition fixture_guarantee := add64_guarantees.\n")
        fixture.write_text(original)
        (project / "C/jet_public_theorems.txt").write_text("C.jet_gate_fixture fixture_guarantee\n")
        (project / "C/jet_contract_definitions.txt").write_text("")
        run(["bash", "build-jets.sh", "--coqc", "C/jet_gate_fixture.v"], project)
        run(["bash", "audit-jet-contracts.sh", "--update"], project)
        run(["bash", "audit-jet-assumptions.sh", "--update"], project)
        fixture.write_text(original.replace(
            "Definition fixture_guarantee :=",
            "Definition fixture_guarantee := fun (_ : (1 = 2)%nat) =>"))
        run(["bash", "build-jets.sh", "--coqc", "C/jet_gate_fixture.v"], project)
        rejected = run(["bash", "audit-jet-contracts.sh"], project, succeeds=False)
        assert "public theorem contracts changed" in rejected.stderr
        # The added premise does not add axioms: reproduce the original bypass.
        run(["bash", "audit-jet-assumptions.sh"], project)
        print("impossible added premise: contract gate rejects, axiom sets unchanged")

        # Retain the original proof term (and thus its axioms) but weaken its
        # proposition to a disjunction with True. The kernel accepts this;
        # acceptance must fail on the changed public type.
        before = "Definition fixture_guarantee := add64_guarantees."
        after = "Definition fixture_guarantee := or_introl (B := True) add64_guarantees."
        assert before in original
        fixture.write_text(original.replace(before, after))
        run(["bash", "build-jets.sh", "--coqc", "C/jet_gate_fixture.v"], project)
        rejected = run(["bash", "audit-jet-contracts.sh"], project, succeeds=False)
        assert "public theorem contracts changed" in rejected.stderr
        run(["bash", "audit-jet-assumptions.sh"], project)
        print("weakened public conclusion: contract gate rejects, axiom sets unchanged")

        # A transparent predicate can change while the named theorem's Check
        # output stays the same. Exercise definition pinning with a tiny,
        # fully proved fixture; never mutate the real checkout.
        fixture.write_text("Require Import C.jet_guarantees.\n"
                           "Definition fixture_post (n : nat) : Prop := n = 0.\n"
                           "Lemma fixture_contract : fixture_post 0. Proof. reflexivity. Qed.\n")
        (project / "C/jet_public_theorems.txt").write_text("C.jet_gate_fixture fixture_contract\n")
        (project / "C/jet_contract_definitions.txt").write_text("C.jet_gate_fixture fixture_post\n")
        run(["bash", "build-jets.sh", "--coqc", "C/jet_gate_fixture.v"], project)
        run(["bash", "audit-jet-contracts.sh", "--update"], project)
        fixture.write_text("Require Import C.jet_guarantees.\n"
                           "Definition fixture_post (n : nat) : Prop := True.\n"
                           "Lemma fixture_contract : fixture_post 0. Proof. exact I. Qed.\n")
        run(["bash", "build-jets.sh", "--coqc", "C/jet_gate_fixture.v"], project)
        rejected = run(["bash", "audit-jet-contracts.sh"], project, succeeds=False)
        assert "public theorem contracts changed" in rejected.stderr
        print("weakened transparent predicate: definition snapshot rejects")

        syntax = Path(work) / "syntax.v"
        for text in (
            "Lemma cheat : False. Proof. Admitted.",
            "Local Axiom cheat : False.",
            "#[local] Axiom cheat : False.",
            "Lemma cheat : False. Proof. admit. Qed.",
            "Lemma cheat : False. Proof. Abort.",
            "Lemma cheat : False. Proof. give_up. Qed.",
            "Unset Guard Checking.",
            "Unset Universe Checking.",
            "Unset Positivity Checking.",
            "#[bypass_check(guard)] Fixpoint cheat : nat := cheat.",
        ):
            syntax.write_text(text)
            run(["python3", "scan-jet-proofs.py", str(syntax)], project, succeeds=False)
        syntax.write_text('(* Admitted. (* Local Axiom x : False. *) *)\n'
                          'Definition label := "Admitted. ""Axiom""".')
        run(["python3", "scan-jet-proofs.py", str(syntax)], project)
        print("inline/local/attributed escape hatches rejected; comments and strings ignored")


if __name__ == "__main__":
    main()
