#!/usr/bin/env python3
"""Reject specification or contract drift in the secp normalize source gate."""
import importlib.util
import shutil
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("secp_gate", SOURCE / "check-secp-normalize-specification.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def main():
    assert gate.check() == 1
    mutations = (
        ("repo", "Haskell/Core/Simplicity/CoreJets.hs", "specificationSecp256k1 FeNormalize = Secp256k1.fe_normalize", "specificationSecp256k1 FeNormalize = Secp256k1.fe_zero"),
        ("repo", "Haskell/Core/Simplicity/Ty/LibSecp256k1.hs", "type FE = Word256", "type FE = Word512"),
        ("repo", "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs", "sub256 = Arith.subtract word256", "sub256 = Arith.subtract word128"),
        ("repo", "Haskell/Core/Simplicity/Programs/LibSecp256k1.hs", ">>> cond ih oh\n\n  , fe_zero", ">>> cond oh ih\n\n  , fe_zero"),
        ("repo", "Haskell/Core/Simplicity/LibSecp256k1/Spec.hs", "fieldOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", "fieldOrder = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30"),
        ("coq", "C/jet_secp_canonical_normalize.v", ">>> cond (I H) (O H)", ">>> cond (O H) (I H)"),
        ("coq", "C/jet_secp_canonical_normalize.v", "@subtract_word_spec term 8", "@subtract_word_spec term 7"),
        ("coq", "C/jet_secp_canonical_normalize.v", "115792089237316195423570985008687907853269984665640564039457584007908834671663", "115792089237316195423570985008687907853269984665640564039457584007908834671662"),
        ("coq", "C/jet_secp_normalize_local.v", "eval_funcall secp_ge", "eval_funcall ge0"),
        ("coq", "C/jet_secp_normalize_local.v", "frame_base_valid sbase ->", "False -> frame_base_valid sbase ->"),
        ("coq", "C/jet_secp_normalize_local.v", "(@canonical_fe_normalize Alg.CoreFunSem).", "(fun a => a)."),
    )
    with tempfile.TemporaryDirectory(prefix="secp-normalize-gate.") as work:
        coq, repo = Path(work) / "Coq", Path(work) / "repo"
        for relative in ("C/jet_secp_canonical_normalize.v", "C/jet_secp_normalize_local.v", "C/jet_bitmachine_rep.v"):
            target = coq / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / relative, target)
        for relative in {path for kind, path, _, _ in mutations if kind == "repo"}:
            target = repo / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(gate.REPO / relative, target)
        assert gate.check(coq, repo) == 1
        for kind, relative, old, new in mutations:
            path = (coq if kind == "coq" else repo) / relative
            original = path.read_text()
            assert old in original, (relative, old)
            path.write_text(original.replace(old, new, 1))
            try:
                gate.check(coq, repo)
            except ValueError:
                pass
            else:
                raise AssertionError(f"accepted mutation: {relative}: {old}")
            finally:
                path.write_text(original)
        assert gate.check(coq, repo) == 1
    print(f"secp normalize specification gate rejected {len(mutations)} mutations")


if __name__ == "__main__":
    main()
