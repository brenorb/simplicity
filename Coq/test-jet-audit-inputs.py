#!/usr/bin/env python3
"""Regression tests for canonical identity and audit input changes."""
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parent


def module(name):
    spec = importlib.util.spec_from_file_location(name, SOURCE / f"{name}.py")
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def main():
    identity = module("check-bitcoin-primitive-identity")
    inputs = module("jet-audit-inputs")
    assert identity.check() == 8
    with tempfile.TemporaryDirectory(prefix="jet-input-tests.") as work:
        root = Path(work)
        coq = root / "Coq"
        coq.mkdir()
        (root / "C").mkdir()
        (root / "Haskell").mkdir()
        model = coq / "model.v"
        canonical = root / "Haskell/Primitive.hs"
        original = identity.MODEL.read_text()
        canonical.write_text(identity.CANONICAL.read_text())
        for old, new in (
            ('primName : string := "Bitcoin"', 'primName : string := "BitcoinExt"'),
            ('CurrentIndex => "currentIndex"', 'CurrentIndex => "wrongName"'),
            ('TapleafVersion : prim Unit Word8', 'TapleafVersion : prim Unit Word32'),
        ):
            assert old in original
            model.write_text(original.replace(old, new))
            try:
                identity.check(model, canonical)
            except ValueError:
                pass
            else:
                raise AssertionError(f"identity gate accepted {new}")
        model.write_text(original)
        assert identity.check(model, canonical) == 8
        baseline = inputs.fingerprint(coq, root)
        for name in ("translation_unit.c", "clightgen-linux.ini.in"):
            path = coq / name
            path.write_text("generation input changed during audit\n")
            assert inputs.fingerprint(coq, root) != baseline
            path.unlink()
        (coq / "model.vo").write_text("compiled output")
        assert inputs.fingerprint(coq, root) == baseline
        for suffix in (".c", ".S", ".s"):
            c_input = root / f"C/input{suffix}"
            c_input.write_text("/* implementation input added during audit */\n")
            assert inputs.fingerprint(coq, root) != baseline
            c_input.unlink()
        canonical_original = canonical.read_text()
        canonical.write_text(canonical_original + "\n-- canonical input edited\n")
        assert inputs.fingerprint(coq, root) != baseline
        canonical.write_text(canonical_original)
        assert inputs.fingerprint(coq, root) == baseline
        model.write_text(original + "\n(* edited during audit *)\n")
        assert inputs.fingerprint(coq, root) != baseline
        candidate = inputs.fingerprint(coq, root, updating=True)
        (coq / "jet_contracts.expected").write_text("candidate snapshot")
        assert inputs.fingerprint(coq, root, updating=True) == candidate
        assert inputs.fingerprint(coq, root) != baseline
    for flags in (("--accept", "--no-build"), ("--accept", "--update-expected")):
        result = subprocess.run(["bash", str(SOURCE / "check-jets.sh"), *flags], capture_output=True, text=True)
        assert result.returncode == 2 and "--accept requires" in result.stderr
    print("audit input tests passed: identity drift, source changes and invalid acceptance modes rejected")


if __name__ == "__main__":
    main()
