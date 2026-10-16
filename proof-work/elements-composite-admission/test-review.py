"""Read-only normal449 contract/source/snapshot/guard/dependency mutations."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal449_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform, binary=False):
    global count
    original = read_bytes(path) if binary else read_text(path)
    altered = transform(original)
    if original == altered:
        raise AssertionError('inactive/no-op normal449 fixture: ' + str(path))
    def text(self, *a, **kw):
        return altered if self == path and not binary else read_text(self, *a, **kw)
    def raw(self, *a, **kw):
        return (altered if binary else altered.encode()) if self == path else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', raw):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted normal449 evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [('coverage_added', 5), ('full_acceptance', True), ('extensions', {}),
                   ('new_sources', []), ('coverage_additions', ''), ('baseline_inputs', {}),
                   ('main_input_sha256', ''), ('main_inputs', {}), ('predecessor_input_sha256', ''),
                   ('predecessor_review_sha256', ''), ('proof_evidence_sha256', {}),
                   ('preparation_engine_sha256', '')]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('coverage_added', 5), ('full_acceptance', True), ('fresh_compiles', {}),
                   ('new_dependencies', {}), ('new_objects_sha256', {})]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace(
    'elements_inputs_hash_program_local_spec', 'elements_inputs_hash_spec_sem'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace(
    '!= elements_composite_contracts()[name]', '== elements_composite_contracts()[name]'))
for folder in g.g.SOURCE_FOLDERS:
    for name in ['check-source.py', 'test-source.py']:
        reject(work / 'Coq/check-jets.sh', lambda t, folder=folder, name=name: t.replace(
            'python3 ' + folder + '/' + name, '# python3 ' + folder + '/' + name))
for name in g.g.GUARDS:
    target = work / 'Coq' / name
    reject(target, lambda text: text + '\n# unreviewed context guard/model\n')
    def altered(self):
        raw = read_bytes(self)
        return raw + b'\nUNREVIEWED\n' if self == target else raw
    with patch.object(Path, 'read_bytes', altered):
        if g.s.inputs.fingerprint(work / 'Coq', work) == fp:
            raise AssertionError('Elements context runtime input omitted from fingerprint: ' + name)
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_application_sep.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_bitcoin_raw_program.v', lambda t: t + '\nUNREVIEWED\n')
for module in g.g.MODULES:
    path = work / 'Coq' / (module.replace('.', '/') + '.v')
    reject(path, lambda text: text + '\nUNREVIEWED\n')
    reject(path.with_suffix('.vo'), lambda raw: raw + b'\x00', binary=True)
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
reject(g.g.PREPARE_ENGINE, lambda t: t + '\n# changed preparation engine\n')


def reject_config(**changes):
    global count
    with patch.multiple(g.CONFIG, **changes):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted invalid normal449 review configuration')


reject_config(ALLOWED_DEPENDENCIES=g.s.SIX | {'Unreviewed.axiom'})
reject_config(ENDPOINT_DEPENDENCIES={})
reject_config(ENDPOINT_DEPENDENCIES={n: set() for n in g.CONFIG.ENDPOINTS})
reject_config(guard_sources=lambda: {})
reject_config(proof_sources=lambda: {})
reject_config(proof_sources=lambda: {n: work / 'Coq' / n for n in g.CONFIG.NEW_SOURCES})
reject_config(proof_sources=lambda: dict(g.g.proof_sources(), **{'C/unreviewed.v': work / 'Coq/C/unreviewed.v'}))
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only normal449 checks changed main/index/private inputs')
print(str(count) + ' normal449 source/snapshot/guard/dependency/evidence corruptions rejected; all6 composite runtime inputs fingerprinted')
