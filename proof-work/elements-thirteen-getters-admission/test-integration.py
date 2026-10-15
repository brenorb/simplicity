"""Read-only installation planning and refusal tests; never forge acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('thirteen_integration_negative', HERE / 'integration.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
count = 0


def reject(action, label):
    global count
    try:
        action()
    except (ValueError, KeyError):
        count += 1
        return
    raise AssertionError('accepted invalid installation prerequisite: ' + label)


def no_write(*a, **kw):
    raise AssertionError('refusal test attempted a write or a subprocess')


# This is a real, reviewed source-only plan, not synthetic positive acceptance.
p = g.plan(work)
assert len(p['targets']) == 23 and p['main_installation'] is False
assert p['actual_main_acceptance'] is False and p['coverage_added'] == 13
assert p['before_inputs'] == before and p['staged_patch_sha256'] == index
assert p['candidate_input_sha256'] == fingerprint
assert all(not name.endswith(('.vo', '.vos', '.vok', '.glob')) for name in p['targets'])

# Missing either real acceptance must stop before planning/installing anything.
original = g.read
with patch.object(g.s, 'changed', no_write):
    for missing in [g.PRED / 'MAIN-ACCEPTANCE.json', work / 'ACCEPTANCE.json']:
        def read(path, missing=missing):
            if path == missing:
                raise ValueError('simulated missing real prerequisite')
            return original(path)
        with patch.object(g, 'read', read):
            reject(lambda: g.install(work), str(missing))
            if missing == work / 'ACCEPTANCE.json':
                # Exercise this guard independently, rather than letting the
                # unfinished predecessor hide the candidate's own guard.
                reject(lambda: g.candidate_acceptance(work), 'candidate receipt independently missing')
    # Test the genuine current state too, but do not run a positive installation
    # when these tests are replayed after the prerequisites have really passed.
    if not (g.PRED / 'MAIN-ACCEPTANCE.json').exists() or not (work / 'ACCEPTANCE.json').exists():
        reject(lambda: g.install(work), 'current unfinished acceptance')
    def installed(path):
        if path == HERE / 'INSTALLATION.json':
            return True
        return exists(path)
    exists = Path.exists
    with patch.object(Path, 'exists', installed):
        reject(lambda: g.install(work), 'already installed')

# All terminal-validation cases use a *real passed* historical acceptance.
# Every modified receipt is negative-only and never passed to an installer.
passed_path = g.PRED / 'ACCEPTANCE.json'
passed = original(passed_path)
for key, value in [('exit_code', 1), ('full_acceptance', False), ('command', ['true']),
                   ('audit_input_sha256', '0' * 64), ('log_sha256', '0' * 64)]:
    def read(path, key=key, value=value):
        return {**passed, key: value} if path == passed_path else original(path)
    with patch.object(g, 'read', read):
        reject(lambda: g.terminal(passed_path, 'full_acceptance', passed['audit_input_sha256']), key)

for replacement in [g.gate.NEW_SOURCES[1], '../outside.v', 'C/copied-object.vo']:
    with patch.object(g.gate, 'NEW_SOURCES', [replacement, *g.gate.NEW_SOURCES[1:]]):
        reject(g.targets, 'duplicate, escaping or compiler-object target: ' + replacement)
review_path = work / 'REVIEW.json'
reviewed = original(review_path)
def review_is_not_acceptance(path):
    return {**reviewed, 'full_acceptance': True} if path == review_path else original(path)
with patch.object(g, 'read', review_is_not_acceptance):
    reject(lambda: g.reviewed_evidence(work), 'review promoted to acceptance')

# The actual-main driver must not launch a subprocess before installation.
sp = importlib.util.spec_from_file_location('thirteen_main_negative', HERE / 'main-accept.py')
main = importlib.util.module_from_spec(sp)
sp.loader.exec_module(main)
with patch.object(main.g.s, 'changed', no_write), patch.object(main.subprocess, 'run', no_write):
    if not (HERE / 'INSTALLATION.json').exists():
        reject(main.main, 'actual-main before installation')
    def launched(path):
        return True if path == HERE / 'MAIN-AUDIT-RUN.json' else exists(path)
    with patch.object(Path, 'exists', launched):
        reject(main.main, 'duplicate actual-main launch')

if (g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only plan/refusal tests changed main/index/candidate')
print(json.dumps(dict(source_only_targets=23, guarded_refusals=count, main_inputs_unchanged=True,
    original_staging_preserved=True, candidate_inputs_unchanged=True,
    positive_installation_exercised=False, full_acceptance_claimed=False), indent=2))
