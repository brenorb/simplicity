"""Negative-only start checks; no invented acceptance, launch, or write."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_getter_start_negative', HERE / 'accept.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
exists = Path.exists
count = 0


def reject(label):
    global count
    try:
        g.main(work)
    except ValueError:
        count += 1
        return
    raise AssertionError('accepted invalid 404 audit start: ' + label)


def forbidden(*a, **kw):
    raise AssertionError('start guard attempted a write or a subprocess')


with patch.object(g.g, 'write', forbidden), patch.object(g.subprocess, 'run', forbidden):
    for missing in [g.g.PRED / 'ACCEPTANCE.json', g.g.PRED / 'INSTALLATION.json']:
        def absent(path, missing=missing):
            return False if path == missing else exists(path)
        with patch.object(Path, 'exists', absent):
            reject(str(missing))
    def launched(path):
        return True if path == work / 'AUDIT-RUN.json' else exists(path)
    with patch.object(Path, 'exists', launched):
        reject('duplicate audit launch')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
    raise ValueError('start guards changed main/index/candidate inputs')
print(json.dumps(dict(guarded_refusals=count, subprocesses_launched=0, writes_attempted=0,
                     positive_acceptance_exercised=False, main_and_candidate_unchanged=True), indent=2))
