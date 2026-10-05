#!/usr/bin/env python3
"""Exercise implementation/specification drift rejection without editing the checkout."""
import hashlib
import importlib.util
import sys
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
    print("source target tests passed: C/spec/config drift and added implementation sources rejected")


if __name__ == "__main__":
    main()
