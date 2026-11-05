#!/usr/bin/env python3
"""Capture a local validation command, executable identity and source manifest.

Run from jet-discovery: python3 tools/run_recorded.py NAME -- COMMAND ARGS...
Outputs reports/data/NAME.{txt,json}. The executable is copied into ignored
build storage so later rebuilds cannot replace a running job's recorded binary.
Source hashes describe the launch checkout; they do not establish a compiler
attestation. Downloaded specifications/vectors remain inert input data.
"""
import datetime
import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    name, separator, *command = sys.argv[1:]
    if separator != "--" or not command or pathlib.Path(name).name != name:
        raise SystemExit("usage: run_recorded.py NAME -- COMMAND ARGS...")
    directory = ROOT / "reports/data"
    directory.mkdir(parents=True, exist_ok=True)
    status = directory / (name + ".json")
    log = directory / (name + ".txt")
    if status.exists() or log.exists():
        raise SystemExit("choose a new run name; existing evidence is preserved")
    executable = pathlib.Path(shutil.which(command[0]) or command[0]).resolve()
    binary_hash = digest(executable)
    copies = ROOT / "dist-newstyle/recorded-executables"
    copies.mkdir(parents=True, exist_ok=True)
    frozen = copies / (binary_hash + "-" + executable.name)
    if not frozen.exists():
        shutil.copy2(executable, frozen)
    paths = [p for base in ["src", "app", "test"] for p in (ROOT / base).rglob("*.hs")]
    paths += [ROOT / p for p in ["jet-discovery.cabal", "cabal.project", "tools/run_recorded.py"]]
    record = {
        "command": command,
        "cwd": str(ROOT),
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "executable": str(executable),
        "executable_sha256": binary_hash,
        "frozen_executable": str(frozen.relative_to(ROOT)),
        "source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)},
        "log": str(log.relative_to(ROOT)),
        "exit_status": None,
    }
    status.write_text(json.dumps(record, indent=2) + "\n")
    print("running " + name, flush=True)
    start = time.monotonic()
    with log.open("wb") as output:
        result = subprocess.run([str(frozen), *command[1:]], cwd=ROOT,
                                stdout=output, stderr=subprocess.STDOUT)
    record.update(exit_status=result.returncode, elapsed_seconds=time.monotonic() - start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  log_sha256=digest(log))
    status.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ["exit_status", "elapsed_seconds", "log", "log_sha256"]}), flush=True)
    raise SystemExit(result.returncode)


if __name__ == "__main__":
    main()
