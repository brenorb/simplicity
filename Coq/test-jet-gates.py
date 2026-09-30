#!/usr/bin/env python3
"""Negative tests for the review's gate bypasses, in an isolated built copy."""
import shutil
import subprocess
import tempfile
from pathlib import Path


def run(args, cwd, succeeds=True):
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if (result.returncode == 0) != succeeds:
        raise RuntimeError(f"unexpected result from {args}:\n{result.stdout}\n{result.stderr}")
    return result


def main():
    source = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix="jet-gate-tests.") as work:
        project = Path(work) / "Coq"
        shutil.copytree(source, project, ignore=shutil.ignore_patterns(
            "__pycache__", "*.glob", "*.aux", "*Makefile*", ".lia.cache"))
        run(["bash", "audit-jet-contracts.sh"], project)
        path = project / "C/jet_guarantees.v"
        original = path.read_text()
        path.write_text(original.replace(
            "Definition add64_guarantees :=",
            "Definition add64_guarantees := fun (_ : (1 = 2)%nat) =>"))
        run(["bash", "build-jets.sh", "--coqc", "-q", "C/jet_guarantees.v"], project)
        rejected = run(["bash", "audit-jet-contracts.sh"], project, succeeds=False)
        assert "public theorem contracts changed" in rejected.stderr
        # The added premise does not add axioms: reproduce the original bypass.
        run(["bash", "audit-jet-assumptions.sh"], project)
        print("impossible added premise: contract gate rejects, axiom sets unchanged")

        syntax = Path(work) / "syntax.v"
        for text in (
            "Lemma cheat : False. Proof. Admitted.",
            "Local Axiom cheat : False.",
            "#[local] Axiom cheat : False.",
            "Lemma cheat : False. Proof. admit. Qed.",
            "Lemma cheat : False. Proof. Abort.",
        ):
            syntax.write_text(text)
            run(["python3", "scan-jet-proofs.py", str(syntax)], project, succeeds=False)
        syntax.write_text('(* Admitted. (* Local Axiom x : False. *) *)\n'
                          'Definition label := "Admitted. ""Axiom""".')
        run(["python3", "scan-jet-proofs.py", str(syntax)], project)
        print("inline/local/attributed escape hatches rejected; comments and strings ignored")


if __name__ == "__main__":
    main()
