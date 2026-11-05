#!/usr/bin/env python3
"""Freeze and run the native UMA bond cohort with the agreed heap cap."""

import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import time

root = Path(__file__).resolve().parents[1]
reports = root / 'reports/data'
name = 'uma-bond-full42-8g'
snapshot = reports / (name + '-freeze')
build = Path('/private/tmp/uma-bond-build')
binary = Path('/private/tmp/uma-bond-smoke')
executable = Path('/private/tmp') / (name + '-frozen') / binary.name

if snapshot.exists():
    raise SystemExit('Existing run snapshot must be preserved')


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


sources = [root / 'src' / path.relative_to(build).with_suffix('.hs')
           for path in build.rglob('*.hi') if path.name != 'Main.hi']
sources.extend(root / 'tools' / filename for filename in
               ('UmaBondSmoke.hs', 'run_uma_bond_vectors.py'))
primary = root / 'vendor-specs/contract-extras'
primary_paths = sorted(primary.glob('UMAprotocol_protocol_c8c3f673_*'))
primary_paths.append(primary / 'provenance.json')
primary_inputs = [{'path': str(path.relative_to(root)), 'sha256': sha256(path)} for path in primary_paths]

inputs = []
for source in sorted(set(sources)):
    relative = source.relative_to(root)
    frozen = snapshot / relative
    frozen.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, frozen)
    inputs.append({'path': str(relative), 'sha256': sha256(source),
                   'snapshot': str(frozen.relative_to(root))})

executable.parent.mkdir(exist_ok=True)
shutil.copy2(binary, executable)
command = [str(executable), '+RTS', '-N1', '-A16m', '-M8G', '-s', '-RTS']
log = reports / (name + '-rts.txt')
provenance = reports / (name + '-provenance.json')
record = {
    'scope': '42 full native bond lifecycle vectors, 41 Store fee arithmetic checks and 11 linked wire/primitive checks',
    'compiler': 'GHC 9.8.4 -O1 -w -threaded -rtsopts -isrc with local package database; diagnostic Main -O0',
    'git_head_at_launch': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip(),
    'command': command,
    'binary_sha256': sha256(executable),
    'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'inputs': inputs,
    'pinned_primary_inputs': primary_inputs,
}
provenance.write_text(json.dumps(record, indent=2) + '\n')
start = time.monotonic()
with log.open('wb') as output:
    result = subprocess.run(command, cwd=root, stdout=output, stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode, elapsed_seconds=time.monotonic() - start,
              completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              log_sha256=sha256(log),
              inputs_unchanged=all(sha256(root / row['path']) == row['sha256'] for row in inputs + primary_inputs))
provenance.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({key: value for key, value in record.items() if key != 'inputs'}, indent=2))
raise SystemExit(result.returncode)
