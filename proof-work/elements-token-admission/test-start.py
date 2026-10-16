"""Read-only combined417 chain and launch refusal tests; no fake acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('combined417_start_negative', HERE / 'accept.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
exists, is_file = Path.exists, Path.is_file
count = 0


def reject(action, label, reason):
    global count
    try:
        action()
    except ValueError as e:
        assert reason in str(e), (label, str(e))
        count += 1
        return
    raise AssertionError('accepted invalid combined417 start: ' + label)


def forbidden(*args, **kwargs):
    raise AssertionError('start refusal attempted a write or subprocess')


chain = g.review_chain(work)
assert len(chain) == 1
with patch.object(g.g, 'write', forbidden), patch.object(g, 'subprocess', SimpleNamespace(run=forbidden)):
    for missing in [g.BASELINE / 'ACCEPTANCE.json', g.BASELINE / 'INSTALLATION.json']:
        def absent(path, missing=missing):
            return False if path == missing else exists(path)
        with patch.object(Path, 'exists', absent):
            reject(lambda: g.main(work), str(missing), 'real isolated415')
    for receipt in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        def launched(path, receipt=receipt):
            return True if path == receipt else exists(path)
        with patch.object(Path, 'exists', launched):
            reject(lambda: g.main(work), 'duplicate audit launch', 'already launched')
    for folder, _, _ in g.BATCHES:
        def absent_review(path, folder=folder):
            return False if path == HERE.parent / folder / 'REVIEW.json' else is_file(path)
        with patch.object(Path, 'is_file', absent_review):
            reject(lambda: g.review_chain(work), 'missing completed review', 'completed six-stage review required')
    wrong = [(g.BATCHES[0][0], 1, g.BATCHES[0][2]), *g.BATCHES[1:]]
    with patch.object(g, 'BATCHES', wrong):
        reject(lambda: g.review_chain(work), 'wrong aggregate scope', 'reviewed chain scope/source/provenance differs')
    reject(lambda: g.review_chain(work.parent / 'wrong417'), 'wrong final candidate', 'wrong final combined candidate')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
    raise ValueError('start guards changed main/index/candidate')
print(json.dumps(dict(guarded_refusals=count, review_chain_sha256=chain,
    acceptance_subprocesses_launched=0, writes_attempted=0,
    positive_acceptance_exercised=False, main_and_candidate_unchanged=True), indent=2))
