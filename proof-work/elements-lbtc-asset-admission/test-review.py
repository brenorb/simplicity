"""Read-only rejection of source/snapshot/evidence/engine corruption."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_normal_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
g.review(work)
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform):
    global count
    original = read_text(path)
    altered = transform(original)
    assert original != altered, path
    def text(self, *a, **kw):
        return altered if self == path else read_text(self, *a, **kw)
    def binary(self, *a, **kw):
        return altered.encode() if self == path else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted lbtc admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('coverage_added', 2), ('full_acceptance', True), ('extensions', {}),
                   ('new_sources', []), ('coverage_additions', ''), ('baseline_inputs', {}),
                   ('main_input_sha256', ''), ('predecessor_input_sha256', ''),
                   ('predecessor_review_sha256', ''), ('proof_preparation_sha256', ''),
                   ('proof_review_sha256', ''), ('preparation_engine_sha256', '')]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('coverage_added', 2), ('full_acceptance', True), ('fresh_compiles', {}),
                   ('new_dependencies', {}), ('new_objects_sha256', {})]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('elements_lbtc_asset_local_spec', 'lbtc_asset_spec_cells'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('name == "simplicity_lbtc_asset"', 'name == "simplicity_transaction_id"'))
for n in ['check-source.py', 'test-source.py']:
    reject(work / 'Coq/check-jets.sh', lambda t, n=n: t.replace('python3 elements-lbtc-asset/' + n, '# python3 elements-lbtc-asset/' + n))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_elements_tappath_nullable.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_elements_lbtc_asset_local.v', lambda t: t.replace('Theorem elements_lbtc_asset_local_spec :', 'Theorem elements_lbtc_asset_local_spec : False ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
reject(g.g.PREPARE_ENGINE, lambda t: t + '\n# changed engine\n')
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('negative checks changed source/index')
print(str(count) + ' lbtc admission/source/printer/snapshot/evidence/engine corruptions rejected')
