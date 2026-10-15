"""Reject output-proof proof-scope/source/terminal-evidence corruptions in memory."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('annex_hash_review_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
r = json.loads((HERE / 'PREPARATION.json').read_text())
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
        raise AssertionError('accepted output-proof evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('namespace', 'AnnexHashReview'), ('normal_registration', True), ('coverage_added', 2),
                   ('full_acceptance', True), ('roots', []), ('new_sources', []), ('fresh_modules', []),
                   ('results', []), ('definitions', []), ('endpoints', []), ('closed_shared_lemmas', []), ('dependencies', {}),
                   ('commands', {}), ('source_sha256', {}), ('object_sha256', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
def truncate(text):
    result = json.loads(text)
    result['results'] = [n.replace("'", '') for n in result['results']]
    return json.dumps(result)
reject(HERE / 'PREPARATION.json', truncate)
reject(work / 'Coq/C/jet_elements_output_proof_literal.v', lambda t: t.replace(
    'Theorem elements_output_surjection_proof_literal_local_spec :', 'Theorem elements_output_surjection_proof_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t + '\nsimplicity_output_surjection_proof WRONG WRONG\n')
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'ast.log', lambda t: t + '\nUNREVIEWED\n')
gate.review()
print(str(count) + ' output-proof scope/apostrophe/source/command/kernel/AST evidence corruptions rejected')
