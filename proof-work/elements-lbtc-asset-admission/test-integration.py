"""Read-only additive 402 plan and refusal checks; no invented acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_install_negative', HERE / 'integration.py')
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
assert len(p['targets']) == 16 and not p['main_installation'] and not p['actual_main_acceptance']
assert p['before_inputs'] == before and p['staged_patch_sha256'] == index and p['candidate_input_sha256'] == fp
original_read, is_file, exists = g.read, Path.is_file, Path.exists
with patch.object(g.s, 'changed', forbidden):
    def absent(path):
        return False if path == g.PRED / 'MAIN-ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(g.predecessor, 'missing actual-main401')
        reject(lambda: g.install(work), 'install before actual-main401')
    def absent(path):
        return False if path == work / 'ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(lambda: g.candidate_acceptance(work), 'missing isolated402')
    def installed(path):
        return True if path == HERE / 'INSTALLATION.json' else exists(path)
    with patch.object(Path, 'exists', installed):
        reject(lambda: g.install(work), 'duplicate install')
    for replacement in [g.g.NEW_SOURCES[0], '../escape.v', 'C/object.vo']:
        with patch.object(g.g, 'GUARDS', [replacement, g.g.GUARDS[1]]):
            reject(g.targets, 'duplicate/escaping/object target')
    def preexisting(path):
        return True if path == g.g.MAIN / g.g.NEW_SOURCES[0] else exists(path)
    with patch.object(Path, 'exists', preexisting):
        reject(lambda: g.plan(work), 'inherited source overwrite')
    for field, value in [('full_acceptance', True), ('preparation_engine_sha256', ''), ('assembly_sha256', '')]:
        rpath = work / 'REVIEW.json'
        reviewed = original_read(rpath)
        def altered(path, field=field, value=value):
            return {**reviewed, field: value} if path == rpath else original_read(path)
        with patch.object(g, 'read', altered):
            reject(lambda: g.reviewed_evidence(work), 'review scope/provenance: ' + field)
    with patch.object(g.s, 'index_hash', lambda: '0' * 64):
        reject(lambda: g.plan(work), 'changed staged patch')

sp = importlib.util.spec_from_file_location('lbtc_actual_main_negative', HERE / 'main-accept.py')
main = importlib.util.module_from_spec(sp)
sp.loader.exec_module(main)
with patch.object(main.g.s, 'changed', forbidden), patch.object(main.subprocess, 'run', forbidden):
    if not (HERE / 'INSTALLATION.json').exists():
        reject(main.main, 'actual-main launch before installation')
    def launched(path):
        return True if path == HERE / 'MAIN-AUDIT-RUN.json' else exists(path)
    with patch.object(Path, 'exists', launched):
        reject(main.main, 'duplicate actual-main launch')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only integration checks changed main/index/candidate')
print(json.dumps(dict(source_only_targets=16, reviewed_overwrites=0, guarded_refusals=count,
    main_inputs_unchanged=True, original_staging_preserved=True, candidate_inputs_unchanged=True,
    positive_installation_exercised=False, full_acceptance_claimed=False), indent=2))
