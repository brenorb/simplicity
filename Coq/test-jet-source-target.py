#!/usr/bin/env python3
"""Exercise implementation/specification drift rejection without editing the checkout."""
import hashlib
import importlib.util
import sys
import subprocess
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
SOURCE = Path(__file__).resolve().parent


def main():
    spec = importlib.util.spec_from_file_location("target", SOURCE / "check-jet-source-target.py")
    target = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(target)
    target.check()
    with tempfile.TemporaryDirectory(prefix="jet-target-tests.") as work:
        root = Path(work)
        (root / "C").mkdir()
        (root / "Haskell").mkdir()
        originals = {"C/frame.c": (target.REPO / "C/frame.c").read_bytes(),
                     "Haskell/spec.hs": b"canonical specification\n"}
        manifest = root / "target.tsv"
        manifest.write_text("".join(f"{name}\t{hashlib.sha256(data).hexdigest()}\n"
                                    for name, data in originals.items()))
        for name, data in originals.items():
            (root / name).write_bytes(data)
        assert target.check(root, manifest, configs=()) == 2
        for name, data in originals.items():
            (root / name).write_bytes(data + b"\nchanged\n")
            try:
                target.check(root, manifest, configs=())
            except ValueError as error:
                assert "source target changed" in str(error)
            else:
                raise AssertionError(f"accepted drift: {name}")
            (root / name).write_bytes(data)
        (root / "C/alternative.c").write_text("alternative implementation\n")
        try:
            target.check(root, manifest, configs=())
        except ValueError as error:
            assert "file set differs" in str(error)
        else:
            raise AssertionError("accepted added implementation source")
        (root / "C/alternative.c").unlink()
        (root / "C/test.c").write_text("test harness\n")
        assert target.check(root, manifest, configs=()) == 2
        config = root / "Coq/C/clightgen-linux.ini.in"
        config.parent.mkdir(parents=True)
        config.write_text("arch=x86\nmodel=64\n")
        config_name = "Coq/C/clightgen-linux.ini.in"
        with manifest.open("a") as file:
            file.write(f"{config_name}\t{hashlib.sha256(config.read_bytes()).hexdigest()}\n")
        assert target.check(root, manifest, configs={config_name}, coq=root / "Coq") == 3
        config.write_text("arch=x86\nmodel=32\n")
        try:
            target.check(root, manifest, configs={config_name}, coq=root / "Coq")
        except ValueError as error:
            assert "source target changed" in str(error)
        else:
            raise AssertionError("accepted configuration drift")
    # Exercise the real default inventory policy, including additions/deletions
    # in every protected category, entirely outside the checkout.
    with tempfile.TemporaryDirectory(prefix="jet-freeze-tests.") as work:
        root = Path(work)
        coq = root / "Coq"
        originals = {
            "C/jet.c": b"production C",
            "Haskell/spec.hs": b"canonical Haskell",
            "Coq/Simplicity/Ty.v": b"input domains",
            "Coq/Simplicity/Primitive/Bitcoin.v": b"primitive identity",
            "Coq/C/jets_elements.v": b"generated AST",
            "Coq/C/regenerate-elements-jets.sh": b"generation flags",
            "Coq/C/jet_elements_translation_unit.c": b"generation harness",
            "Coq/C/clightgen-linux.ini.in": b"compiler configuration",
            "Coq/jet-deps.sh": b"toolchain pins",
            "Coq/jet-sysroot.sh": b"header pins",
        }
        manifest = root / "target.tsv"
        manifest.write_text("".join(f"{name}\t{hashlib.sha256(data).hexdigest()}\n"
                                    for name, data in originals.items()))
        for name, data in originals.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)

        def check():
            return target.check(root, manifest, coq=coq)

        def rejects(label):
            try:
                check()
            except (ValueError, OSError):
                return
            raise AssertionError(f"accepted {label}")

        assert check() == len(originals)
        for name, data in originals.items():
            path = root / name
            path.write_bytes(data + b" changed")
            rejects(f"modified {name}")
            path.unlink()
            rejects(f"deleted {name}")
            path.write_bytes(data)
        for name in ("C/extra.h", "Haskell/extra.hs", "Coq/Simplicity/Extra.v",
                     "Coq/C/jets_alternative.v", "Coq/C/regenerate-alternative.sh",
                     "Coq/C/jet_extra_translation_unit.c", "Coq/C/clightgen-other.ini.in"):
            path = root / name
            path.write_bytes(b"new target")
            rejects(f"added {name}")
            path.unlink()
        # Unchanged bytes through a symlink must not become an external target.
        path = root / "Coq/Simplicity/Ty.v"
        external = root / "outside.v"
        external.write_bytes(path.read_bytes())
        path.unlink()
        path.symlink_to(external)
        rejects("symlink target")
        path.unlink()
        path.write_bytes(originals["Coq/Simplicity/Ty.v"])
        # Proof support and tests remain editable.
        (coq / "C/jet_new_proof.v").write_text("proof support")
        (root / "C/test.c").write_text("test harness")
        assert check() == len(originals)
        saved = manifest.read_bytes()
        manifest.write_text("C/jet.c\tnot-a-sha256\n")
        rejects("malformed manifest digest")
        manifest.write_bytes(saved)
    # Check the actual CLI fails on a manifest-only edit before inspecting files.
    with tempfile.TemporaryDirectory(prefix="jet-manifest-tests.") as work:
        root = Path(work)
        (root / "C").mkdir()
        checker = root / "check-jet-source-target.py"
        checker.write_bytes((SOURCE / checker.name).read_bytes())
        (root / "C/jet_source_target.tsv").write_bytes(
            (SOURCE / "C/jet_source_target.tsv").read_bytes() + b"\n")
        result = subprocess.run([sys.executable, str(checker)], capture_output=True, text=True)
        assert result.returncode != 0
        assert "frozen source-target manifest changed" in result.stderr, result.stderr
    print("source target tests passed: production/specification/AST/config mutations, "
          "additions, deletions and symlinks rejected; proof support remains editable")


if __name__ == "__main__":
    main()
