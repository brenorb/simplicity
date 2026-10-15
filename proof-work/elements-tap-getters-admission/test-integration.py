"""Read-only 401 delta plan and independent refusal/repair-boundary checks."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tap_install_negative', HERE / 'integration.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
count = 0


def reject(action, label):
    global count
    try:
        action()
    except (ValueError, KeyError):
        count += 1
        return
    raise AssertionError('accepted invalid integration condition: ' + label)


def forbidden(*a, **kw):
    raise AssertionError('refusal/planning test attempted a write or subprocess')


p = g.plan(work)
assert len(p['targets']) == 15 and p['main_installation'] is False and p['actual_main_acceptance'] is False
assert p['before_inputs'] == before and p['staged_patch_sha256'] == index and p['candidate_input_sha256'] == fp
assert set(p['reviewed_source_generalization']) == {'C/jet_elements_tappath_nullable.v'}
original_read, is_file, exists = g.read, Path.is_file, Path.exists
with patch.object(g.s, 'changed', forbidden):
    # Test each missing real prerequisite independently, never fabricating a
    # successful acceptance or invoking a positive install.
    def absent(path):
        return False if path == g.PRED / 'MAIN-ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(g.predecessor, 'missing actual-main 399')
        reject(lambda: g.install(work), 'install before actual-main 399')
    def absent(path):
        return False if path == work / 'ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(lambda: g.candidate_acceptance(work), 'missing isolated 401')
    def installed(path):
        return True if path == HERE / 'INSTALLATION.json' else exists(path)
    with patch.object(Path, 'exists', installed):
        reject(lambda: g.install(work), 'duplicate installation')
    for replacement in [g.g.NEW_SOURCES[0], '../escape.v', 'C/object.vo']:
        with patch.object(g.g, 'GUARDS', [replacement, g.g.GUARDS[1]]):
            reject(g.targets, 'duplicate/escaping/object target')
    with patch.object(g.g, 'MODIFIED_SOURCES', ['C/jet_elements_prim.v']):
        reject(g.targets, 'broadened inherited overwrite')
    meta_path = work / 'ASSEMBLY.json'
    meta = original_read(meta_path)
    for field in ['before', 'after']:
        fake = json.loads(json.dumps(meta))
        fake['reviewed_source_generalization']['C/jet_elements_tappath_nullable.v'][field] = '0' * 64
        def altered(path, fake=fake):
            return fake if path == meta_path else original_read(path)
        with patch.object(g, 'read', altered):
            reject(lambda: g.plan(work), 'wrong reviewed nullable ' + field)
    fake = {**meta, 'reviewed_source_generalization': {}}
    def altered(path):
        return fake if path == meta_path else original_read(path)
    with patch.object(g, 'read', altered):
        reject(lambda: g.plan(work), 'unrecorded inherited overwrite')
    rpath = work / 'REVIEW.json'
    reviewed = original_read(rpath)
    def altered(path):
        return {**reviewed, 'full_acceptance': True} if path == rpath else original_read(path)
    with patch.object(g, 'read', altered):
        reject(lambda: g.reviewed_evidence(work), 'review promoted to full acceptance')

sp = importlib.util.spec_from_file_location('tap_actual_main_negative', HERE / 'main-accept.py')
main = importlib.util.module_from_spec(sp)
sp.loader.exec_module(main)
with patch.object(main.g.s, 'changed', forbidden), patch.object(main.subprocess, 'run', forbidden):
    if not (HERE / 'INSTALLATION.json').exists():
        reject(main.main, 'actual-main launch before installation')
    def launched(path):
        return True if path == HERE / 'MAIN-AUDIT-RUN.json' else exists(path)
    with patch.object(Path, 'exists', launched):
        reject(main.main, 'duplicate main launch')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only integration checks changed main/index/candidate')
print(json.dumps(dict(source_only_targets=15, reviewed_overwrites=1, guarded_refusals=count,
    main_inputs_unchanged=True, original_staging_preserved=True, candidate_inputs_unchanged=True,
    positive_installation_exercised=False, full_acceptance_claimed=False), indent=2))
