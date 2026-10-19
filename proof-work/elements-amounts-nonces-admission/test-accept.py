"""Read-only tests of the full470 launch boundary; never launch an audit.

Validate the real complete chain first. Cache that real predecessor only in
unit mutations; production accept.py revalidates every prerequisite.
"""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal470_accept_negative', HERE / 'accept.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
chain = g.prerequisites(work)
review = json.loads((HERE / 'REVIEW.json').read_text())
inherited = g.prior.prerequisites(g.g.BASE_TREE)
read_text, read_bytes, is_file = Path.read_text, Path.read_bytes, Path.is_file
count = 0


def reject(call):
    global count
    try:
        call()
    except (ValueError, KeyError):
        count += 1
        return
    raise AssertionError('accepted full470 audit-boundary corruption')


def corrupt(paths, key, value, call):
    changed = {}
    for path in paths:
        record = json.loads(read_text(path))
        if record.get(key) == value:
            raise AssertionError('inactive full470 receipt fixture: ' + key)
        record[key] = value
        changed[path] = json.dumps(record)
    def text(self, *args, **kwargs):
        return changed[self] if self in changed else read_text(self, *args, **kwargs)
    def raw(self, *args, **kwargs):
        return changed[self].encode() if self in changed else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', raw):
        reject(call)


for missing in [g.ROOT447_FOLDER / 'ACCEPTANCE.json', HERE / 'REVIEW.json', g.g.PRED / 'REVIEW.json']:
    with patch.object(Path, 'is_file', lambda self: False if self == missing else is_file(self)):
        reject(lambda: g.prerequisites(work))

with patch.object(g.prior, 'prerequisites', return_value=inherited):
    for field, value in [('combined_delta_jets', 19), ('full449_acceptance_claimed', True)]:
        with patch.object(g.prior, 'prerequisites', return_value=dict(inherited, **{field: value})):
            reject(lambda: g.prerequisites(work))
    # The real independent review passed above; isolate the receipt layer here.
    with patch.object(g.v, 'review', return_value=review['review']):
        for key, value in [('full_acceptance', True), ('assembly_sha256', ''),
                           ('preparation_sha256', ''), ('preparation_engine_sha256', ''),
                           ('review_engine_sha256', ''), ('candidate_input_sha256', ''),
                           ('tools_sha256', {}), ('evidence_sha256', {}), ('checks', {})]:
            corrupt([HERE / 'REVIEW.json', work / 'REVIEW.json'], key, value, lambda: g.reviewed(work))
        changed_checks = dict(review['checks'])
        changed_checks['coverage'] = dict(changed_checks['coverage'], command=['true'])
        corrupt([HERE / 'REVIEW.json', work / 'REVIEW.json'], 'checks', changed_checks,
                lambda: g.reviewed(work))

if (g.prerequisites(work) != chain or g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only full470 launch tests changed reviewed evidence/main/index')
print(str(count) + ' full470 missing-terminal, predecessor-scope, provenance and eight-stage-review corruptions rejected')
