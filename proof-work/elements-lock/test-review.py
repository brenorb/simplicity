"""Reject lock receipt/source corruptions in memory, without invalid proofs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('lock_review_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
record = json.loads((HERE / 'PREPARATION.json').read_text())
work = Path(record['candidate'])
read_text, read_bytes = Path.read_text, Path.read_bytes
rejected = 0


def reject(path, transform):
    global rejected
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
            rejected += 1
            return
        raise AssertionError('accepted lock evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('namespace', 'C'), ('normal_registration', True), ('coverage_added', 2),
                   ('full_acceptance', True), ('fresh_modules', []), ('modules', []),
                   ('results', []), ('definitions', []), ('pure_results', []),
                   ('dependencies', {}), ('commands', {}), ('source_sha256', {}),
                   ('object_sha256', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'ast.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'source-negative.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Proof/jet_elements_lock_literal.v', lambda t: t.replace(
    'Theorem elements_tx_lock_time_literal_local_spec :',
    'Theorem elements_tx_lock_time_literal_local_spec : False ->'))
reject(HERE / 'source/jet_elements_lock_literal.v.source', lambda t: t.replace(
    'haskell_to_word 5 500000000', 'haskell_to_word 5 500000001'))
reject(work / 'Coq/C/jet_elements_lock_local.v', lambda t: t.replace(
    'Theorem elements_tx_lock_height_local_spec :',
    'Theorem elements_tx_lock_height_local_spec : False ->'))
gate.review()
print(str(rejected) + ' lock namespace/source/command/bridge/kernel/AST evidence corruptions rejected')
