"""Reject altered formal checkpoint evidence without compiling bad proofs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('issuance_review_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
r = json.loads((HERE / 'CHECKED.json').read_text())
work = Path(r['candidate'])
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform):
    global count
    original = read_text(path)
    altered = transform(original)
    assert original != altered, path
    def text(self, *args, **kwargs):
        return altered if self == path else read_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return altered.encode() if self == path else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            gate.review()
        except (ValueError, KeyError):
            count += 1
            return
        raise AssertionError('accepted issuance evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [('source_fidelity_review_complete', True), ('normal_registration', True), ('coverage_added', 4),
                   ('full_acceptance', True), ('new_source', 'C/jet_elements_prim.v'), ('roots', []),
                   ('fresh_modules', []), ('reused_checked_modules', []), ('results', []), ('definitions', []),
                   ('endpoints', []), ('original_endpoints', []), ('closed_view_lemmas', []),
                   ('dependencies', {}), ('commands', {}), ('tools_sha256', {}), ('source_sha256', ''), ('object_sha256', '')]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(work / 'Coq/C/jet_elements_issuance_proof_literal.v', lambda t: t.replace(
    'Theorem elements_current_issuance_token_proof_literal_local_spec :',
    'Theorem elements_current_issuance_token_proof_literal_local_spec : False ->'))
reject(HERE / 'source/jet_elements_issuance_proof_literal.v.source', lambda t: t.replace('if token then []', 'if token then [Byte.zero]'))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t + '\nsimplicity_issuance_asset_proof WRONG WRONG\n')
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'ast.log', lambda t: t + '\nUNREVIEWED\n')
gate.review()
print(str(count) + ' issuance scope/source/command/kernel/AST evidence corruptions rejected')
