"""Read-only normal420 source/snapshot/Ready/dependency/evidence mutations."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_normal_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
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
    raise AssertionError('accepted initialized lambda normal corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('coverage_added', 2), ('full_acceptance', True), ('extensions', {}),
                   ('new_sources', []), ('coverage_additions', ''), ('baseline_inputs', {}),
                   ('main_input_sha256', ''), ('main_inputs', {}), ('predecessor_input_sha256', ''),
                   ('predecessor_review_sha256', ''), ('proof_evidence_sha256', {}),
                   ('preparation_engine_sha256', '')]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('coverage_added', 2), ('full_acceptance', True), ('fresh_compiles', {}),
                   ('new_dependencies', {}), ('new_objects_sha256', {})]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace(
    'scalar_lambda_initialized_local_spec', 'scalar_lambda_runs_from_actual_init'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace(
    'name == "simplicity_scalar_multiply_lambda"', 'name == "simplicity_scalar_square"'))
for n in ['check-lambda-public.py', 'test-lambda-public.py']:
    reject(work / 'Coq/check-jets.sh', lambda t, n=n: t.replace(
        'python3 scalar-lambda-integration/' + n, '# python3 scalar-lambda-integration/' + n))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_elements_null_data_contract.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_clight_forward.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_frame_constructible.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_secp_scalar_lambda_local.v', lambda t: t.replace(
    'secp_jet_initialized_local_spec scalar_lambda_initialized', 'secp_jet_local_spec'))
reject(work / 'Coq/C/jet_secp_initialized_contract.v', lambda t: t.replace('Ready m ->', 'True ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
reject(g.g.PREPARE_ENGINE, lambda t: t + '\n# changed engine\n')


def reject_config(**changes):
    global count
    with patch.multiple(g.CONFIG, **changes):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted invalid dependency configuration')


reject_config(ALLOWED_DEPENDENCIES=g.CONFIG.ALLOWED_DEPENDENCIES | {'Unreviewed.axiom'})
reject_config(ALLOWED_DEPENDENCIES=g.s.SIX)
reject_config(ENDPOINT_DEPENDENCIES={})
reject_config(ENDPOINT_DEPENDENCIES={n: g.s.SIX for n in g.CONFIG.ENDPOINTS})
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only normal checks changed main/index/candidate')
print(str(count) + ' initialized-lambda normal/source/Ready/dependency/evidence corruptions rejected')
