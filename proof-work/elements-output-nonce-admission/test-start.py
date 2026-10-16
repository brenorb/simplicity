"""Real reviewed combined candidate; refusal tests never launch acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('nonce_combined_start_negative', HERE / 'accept.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
exists, is_file = Path.exists, Path.is_file
count = 0


def reject(label, reason):
    global count
    try:
        g.main(work)
    except ValueError as e:
        assert reason in str(e), (label, str(e))
        count += 1
        return
    raise AssertionError('accepted invalid combined407 start: ' + label)


def forbidden(*a, **kw):
    raise AssertionError('start refusal attempted a write or subprocess')


with patch.object(g.g, 'write', forbidden), patch.object(g, 'subprocess', SimpleNamespace(run=forbidden)):
    for missing in [g.BASELINE / 'ACCEPTANCE.json', g.BASELINE / 'INSTALLATION.json']:
        def absent(path, missing=missing):
            return False if path == missing else exists(path)
        with patch.object(Path, 'exists', absent):
            reject(str(missing), 'real isolated401')
    for receipt in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        def launched(path, receipt=receipt):
            return True if path == receipt else exists(path)
        with patch.object(Path, 'exists', launched):
            reject('duplicate audit launch', 'already launched')
    def absent_review(path):
        return False if path == HERE / 'REVIEW.json' else is_file(path)
    with patch.object(Path, 'is_file', absent_review):
        reject('missing completed407 review', 'completed six-stage review required')
    wrong = [(g.BATCHES[0][0], 2, g.BATCHES[0][2]), *g.BATCHES[1:]]
    with patch.object(g, 'BATCHES', wrong):
        reject('wrong cumulative delta scope', 'reviewed chain scope/source/provenance differs')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
    raise ValueError('start guards changed main/index/candidate')
print(json.dumps(dict(guarded_refusals=count, acceptance_subprocesses_launched=0, writes_attempted=0,
    positive_acceptance_exercised=False, main_and_candidate_unchanged=True), indent=2))
