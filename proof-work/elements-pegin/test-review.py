"""Reject pegin scope/name/tag/source/compiler/kernel evidence corruptions."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pegin_review_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
record = json.loads((HERE / 'PREPARATION.json').read_text())
work = Path(record['candidate'])
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
        raise AssertionError('accepted pegin evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('namespace', 'C'), ('normal_registration', True), ('coverage_added', 2),
                   ('full_acceptance', True), ('fresh_modules', []), ('roots', []),
                   ('originals', []), ('finals', []), ('results', []), ('definitions', []),
                   ('dependencies', {}), ('commands', {}), ('source_sha256', {}),
                   ('object_sha256', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
def truncate_names(text):
    r = json.loads(text)
    r['results'] = [n.replace("'", '') for n in r['results']]
    return json.dumps(r)
reject(HERE / 'PREPARATION.json', truncate_names)
reject(work / 'Proof/jet_elements_pegin_literal.v', lambda t: t.replace(
    'Theorem elements_input_pegin_literal_local_spec :', 'Theorem elements_input_pegin_literal_local_spec : False ->'))
reject(HERE / 'source/jet_elements_pegin_literal.v.source', lambda t: t.replace(
    'haskell_from_word 5 a', 'haskell_from_word 4 a'))
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'ast.log', lambda t: t + '\nUNREVIEWED\n')
gate.review()
print(str(count) + ' pegin scope/apostrophe/source/command/kernel/AST corruptions rejected')
