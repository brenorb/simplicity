"""Read-only refreshed-lambda source/provenance/scope/command rejection tests."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_refresh_negative', HERE / 'review.py')
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
    assert altered != original, path
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
    raise AssertionError('accepted refreshed-lambda evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('recursive_kernel_check', False), ('canonical_source_guard', False), ('normal_registration', True),
                   ('coverage_added', 1), ('full_acceptance', True), ('results', []), ('definitions', []),
                   ('dependencies', {}), ('fresh_modules', []), ('commands', {}), ('source_sha256', {}),
                   ('object_sha256', {}), ('candidate_input_sha256', ''), ('staged_patch_sha256', ''),
                   ('assembly_sha256', ''), ('tools_sha256', {})]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(HERE / 'ASSEMBLY.json', field('old_assembly_sha256', ''))
reject(work / 'Coq/C/jet_secp_initialized_contract.v', lambda t: t.replace('Ready m ->', 'True ->'))
reject(work / 'Coq/C/jet_secp_scalar_lambda_global.v', lambda t: t.replace('37718080363155996902926221483475020450927657555482586988616620542887997980018', '1'))
reject(work / 'Coq/C/jet_frame_constructible.v', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'lambda-refresh-contracts.log', lambda t: t + '\n...\n')
reject(work / 'lambda-refresh-assumptions.log', lambda t: t.replace('Classical_Prop.classic', 'Unreviewed.axiom'))
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'source.log', lambda t: t + '\nUNREVIEWED\n')
reject(HERE / 'check.py', lambda t: t + '\n# changed checker\n')
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only refresh tests changed main/index/candidate')
print(str(count) + ' refreshed-lambda source/provenance/scope/command corruptions rejected')
