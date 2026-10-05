#!/usr/bin/env python3
"""Reject catalog, recursion and vector-depth drift without editing the checkout."""
import importlib.util
import shutil
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("fullshift", ROOT / "check-fullshift-specification.py")
fullshift = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fullshift)


def main():
    assert fullshift.check() == 36
    with tempfile.TemporaryDirectory(prefix="fullshift-spec.") as work:
        repo = Path(work)
        coq = repo / "Coq"
        files = [
            (fullshift.REPO / "Haskell/Core/Simplicity/CoreJets.hs", repo / "Haskell/Core/Simplicity/CoreJets.hs"),
            (fullshift.REPO / "Haskell/Core/Simplicity/Programs/Word.hs", repo / "Haskell/Core/Simplicity/Programs/Word.hs"),
            *[(ROOT / name, coq / name) for name in
              ("Simplicity/Word.v", "C/jet_core_fullshift_jets.v", "C/jet_core_fullshift64_jets.v")],
        ]
        for src, dst in files:
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src, dst)
        assert fullshift.check(coq, repo) == 36
        for path, old, new in (
            (repo / "Haskell/Core/Simplicity/CoreJets.hs", "FullLeftShift64_1 = Prog.full_shift word64 word1",
             "FullLeftShift64_1 = Prog.full_shift word1 word64"),
            (coq / "C/jet_core_fullshift64_jets.v", "(@full_left_shift1 (Word 0) 6 Alg.CoreFunSem)",
             "(@full_left_shift1 (Word 0) 5 Alg.CoreFunSem)"),
            (coq / "Simplicity/Word.v", "| S n => build_full_left_shift1 full_left_shift1",
             "| S n => build_full_right_shift1 full_right_shift1"),
        ):
            original = path.read_text()
            assert old in original
            path.write_text(original.replace(old, new, 1))
            try:
                fullshift.check(coq, repo)
            except ValueError:
                pass
            else:
                raise AssertionError(f"accepted full_shift drift: {new}")
            path.write_text(original)
    print("full_shift tests passed: catalog, vector depth and recursive dispatch drift rejected")


if __name__ == "__main__":
    main()
