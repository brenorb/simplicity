#!/usr/bin/env python3
"""Run unchanged upstream suites; C products stay in an ignored archive copy.

Invoke from jet-discovery inside its Nix shell. No downloaded source is run.
QuickCheck uses its upstream default number of cases; no test-name filter.
"""
import hashlib
import json
import pathlib
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
REPO = ROOT.parent
DATA = ROOT / "reports/data"
SCRATCH = ROOT / "dist-newstyle/upstream-c-validation"
DATA.mkdir(parents=True, exist_ok=True)
SCRATCH.mkdir(parents=True, exist_ok=True)


def git(*args):
    return subprocess.check_output(["git", *args], cwd=REPO, text=True).strip()


record = {
    "source_commit": git("rev-parse", "HEAD"),
    "c_tree": git("rev-parse", "HEAD:C"),
    "haskell_tree": git("rev-parse", "HEAD:Haskell"),
    "haskell_source_diff": git("diff", "HEAD", "--", "Haskell", "Simplicity.cabal", "C"),
    "quickcheck_cases": "upstream default; no override",
    "test_filter": "none",
    "test_project_sha256": hashlib.sha256((ROOT / "cabal.upstream-tests.project").read_bytes()).hexdigest(),
    "runs": [],
}
if record["haskell_source_diff"]:
    raise SystemExit("Frozen upstream sources differ from HEAD; inspect before testing")


def run(name, args, cwd):
    target = DATA / (name + ".txt")
    print("running " + name, flush=True)
    start = time.monotonic()
    with target.open("w") as log:
        result = subprocess.run(args, cwd=cwd, stdout=log, stderr=subprocess.STDOUT)
    row = dict(name=name, command=args, cwd=str(cwd), exit_status=result.returncode,
               elapsed_seconds=time.monotonic() - start,
               log=str(target.relative_to(ROOT)), sha256=hashlib.sha256(target.read_bytes()).hexdigest())
    record["runs"].append(row)
    (DATA / "upstream-validation-status.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(row), flush=True)
    return result.returncode


archive = SCRATCH / "upstream-c.tar"
with archive.open("wb") as stream:
    subprocess.run(["git", "archive", "HEAD", "C"], cwd=REPO, stdout=stream, check=True)
subprocess.run(["tar", "-xf", str(archive), "-C", str(SCRATCH)], check=True)
failures = [run("upstream-c-default-check", ["make", "-j4", "check", "doCheck=1"], SCRATCH / "C")]
# Force the generated executable to relink with the explicit RTS link flag.
# This does not remove source, test objects, or any file in a frozen tree.
for generated in (ROOT / "dist-newstyle/upstream-haskell/build").glob("*/ghc-*/Simplicity-*/t/testsuite/build/testsuite/testsuite"):
    generated.unlink()
failures.append(run("upstream-haskell-default-tests", [
    "cabal", "test", "Simplicity:test:testsuite", "--project-file=cabal.upstream-tests.project", "--builddir=dist-newstyle/upstream-haskell", "--ghc-options=-rtsopts", "--test-show-details=direct",
    "--test-option=--num-threads=2", "--test-option=+RTS", "--test-option=-N2",
    "--test-option=-M12G", "--test-option=-RTS"], ROOT))
raise SystemExit(1 if any(failures) else 0)
