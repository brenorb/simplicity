"""Read-only combined418 planning and refusal tests; no invented acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('combined418_install_negative', HERE / 'integration.py')
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


def forbidden(*args, **kwargs):
    raise AssertionError('read-only test attempted a write or subprocess')


p = g.plan(work)
assert len(p['targets']) == 22 and not p['main_installation'] and not p['full_acceptance']
assert p['staged_patch_sha256'] == index and p['candidate_input_sha256'] == fp
assert g.reviewed_evidence(work)[0] == p
if (g.PRED / 'MAIN-ACCEPTANCE.json').is_file():
    assert g.predecessor()[1]['actual_main_acceptance'] is True
original_read, is_file, exists = g.read, Path.is_file, Path.exists
with patch.object(g.s, 'changed', forbidden):
    def absent(path):
        return False if path == g.PRED / 'MAIN-ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(g.predecessor, 'missing actual-main415')
        reject(lambda: g.install(work), 'install before actual-main415')
    def absent(path):
        return False if path == work / 'ACCEPTANCE.json' else is_file(path)
    with patch.object(Path, 'is_file', absent):
        reject(lambda: g.candidate_acceptance(work), 'missing isolated418')
        reject(lambda: g.install(work), 'install before isolated418')
    def installed(path):
        return True if path == HERE / 'INSTALLATION.json' else exists(path)
    with patch.object(Path, 'exists', installed):
        reject(lambda: g.install(work), 'duplicate install')

    configs = {HERE.parent / folder / 'admission.py': g.load('negative_config_' + prefix,
               HERE.parent / folder / 'admission.py') for folder, _, prefix in g.a.BATCHES}
    original_load = g.load
    first = next(iter(configs))
    config = configs[first]
    for replacement in [config.NEW_SOURCES[0], '../escape.v', '/private/tmp/escape.v', 'C/object.vo',
                        'C/object.vos', 'C/object.vok', 'C/object.glob']:
        altered = SimpleNamespace(METADATA=config.METADATA, SCRIPTS=config.SCRIPTS,
            GUARDS=[replacement, config.GUARDS[1]], NEW_SOURCES=config.NEW_SOURCES)
        def load(name, path, altered=altered):
            return altered if path == first else original_load(name, path)
        with patch.object(g, 'load', load):
            reject(g.targets, 'duplicate/escaping/object target: ' + replacement)
    def preexisting(path):
        return True if path == g.g.MAIN / config.NEW_SOURCES[0] else exists(path)
    with patch.object(Path, 'exists', preexisting):
        reject(lambda: g.plan(work), 'inherited source overwrite')

    for field, value in [('main_installation', True), ('full_acceptance', True), ('coverage_added', 1),
                         ('inherited_proof_overwrites', 1), ('compiler_objects_copied', 1),
                         ('candidate_input_sha256', '0' * 64), ('after_sha256', {})]:
        def altered(path, field=field, value=value):
            return {**p, field: value} if path == HERE / 'INSTALLATION-PLAN.json' else original_read(path)
        with patch.object(g, 'read', altered):
            reject(lambda: g.reviewed_evidence(work), 'plan scope/provenance: ' + field)
    for field, value in [('full_acceptance', True), ('preparation_engine_sha256', ''),
                         ('assembly_sha256', ''), ('checks', {})]:
        rpath = HERE / 'REVIEW.json'
        reviewed = original_read(rpath)
        def altered(path, field=field, value=value):
            return {**reviewed, field: value} if path == rpath else original_read(path)
        with patch.object(g, 'read', altered):
            reject(lambda: g.reviewed_evidence(work), 'review scope/provenance: ' + field)
    with patch.object(g.s, 'index_hash', lambda: '0' * 64):
        reject(lambda: g.plan(work), 'changed staged patch')

sp = importlib.util.spec_from_file_location('combined418_actual_main_negative', HERE / 'main-accept.py')
main = importlib.util.module_from_spec(sp)
sp.loader.exec_module(main)
# Replace this module's subprocess binding, not the globally shared subprocess
# module: read-only git check_output calls remain available to the guards.
with patch.object(main.g.s, 'changed', forbidden), patch.object(main, 'subprocess', SimpleNamespace(run=forbidden)):
    if not (HERE / 'INSTALLATION.json').exists():
        reject(main.main, 'actual-main launch before installation')
    def launched(path):
        return True if path == HERE / 'MAIN-AUDIT-RUN.json' else exists(path)
    with patch.object(Path, 'exists', launched):
        reject(main.main, 'duplicate actual-main launch')
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only integration tests changed main/index/candidate')
print(json.dumps(dict(source_only_targets=22, reviewed_overwrites=0, guarded_refusals=count,
    main_inputs_unchanged=True, original_staging_preserved=True, candidate_inputs_unchanged=True,
    positive_installation_exercised=False, full_acceptance_claimed=False), indent=2))
