"""Read-only full-audit boundary regressions, never a replacement for an audit.

Validate the real chain first. Unit mutations then cache only that unchanged
expensive predecessor/delta check; production accept.py always revalidates it.
"""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal467_accept_negative', HERE / 'accept.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
chain = g.prerequisites(work)
review = json.loads((HERE / 'REVIEW.json').read_text())
prior_launch = json.loads((g.ROOT447_FOLDER / 'AUDIT-RUN.json').read_text())
read_text, read_bytes, is_file = Path.read_text, Path.read_bytes, Path.is_file
count = 0


def reject(call):
    global count
    try:
        call()
    except (ValueError, KeyError):
        count += 1
        return
    raise AssertionError('accepted full467 audit-boundary corruption')


def corrupt(paths, key, value, call):
    changed = {}
    for path in paths:
        r = json.loads(read_text(path))
        if r.get(key) == value:
            raise AssertionError('inactive full467 terminal fixture: ' + key)
        r[key] = value
        changed[path] = json.dumps(r)
    def text(self, *a, **kw):
        return changed[self] if self in changed else read_text(self, *a, **kw)
    def raw(self, *a, **kw):
        return changed[self].encode() if self in changed else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', raw):
        reject(call)


for missing in [g.ROOT447_FOLDER / 'ACCEPTANCE.json', HERE / 'REVIEW.json']:
    with patch.object(Path, 'is_file', lambda self: False if self == missing else is_file(self)):
        reject(lambda: g.prerequisites(work))

# Both receipt copies are corrupted identically: not just the copy-equality check.
with patch.object(g.prior.prior, 'prerequisites', return_value=prior_launch['review_chain']):
    for name, fields in [
        ('AUDIT-RUN.json', [('command', ['true']), ('audit_input_sha256', ''),
                            ('review_chain', {}), ('driver_sha256', ''),
                            ('full_acceptance', True), ('main_installation', True)]),
        ('TERMINAL.json', [('exit_code', 1), ('seconds', 0), ('log_sha256', '')]),
        ('ACCEPTANCE.json', [('full_acceptance', False), ('coverage', '467/533'), ('exit_code', 1)]),
    ]:
        for key, value in fields:
            corrupt([g.ROOT447_FOLDER / name, g.ROOT447_TREE / name], key, value, g.predecessor447)

# The independent review was really run above. These mutations test the launch
# receipt layer without rerunning all source-mutation suites for each fixture.
with patch.object(g.v, 'review', return_value=review['review']):
    for key, value in [('full_acceptance', True), ('assembly_sha256', ''),
                       ('preparation_sha256', ''), ('preparation_engine_sha256', ''),
                       ('review_engine_sha256', ''), ('candidate_input_sha256', ''),
                       ('tools_sha256', {}), ('evidence_sha256', {}), ('checks', {})]:
        corrupt([HERE / 'REVIEW.json', work / 'REVIEW.json'], key, value, lambda: g.reviewed(work))
    changed_checks = dict(review['checks'])
    changed_checks['coverage'] = dict(changed_checks['coverage'], command=['true'])
    corrupt([HERE / 'REVIEW.json', work / 'REVIEW.json'], 'checks', changed_checks, lambda: g.reviewed(work))

if (g.prerequisites(work) != chain or g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only full467 launch tests changed reviewed evidence/main/index')
print(str(count) + ' full467 missing-terminal, successful-exit, provenance, scope and six-stage-review corruptions rejected')
