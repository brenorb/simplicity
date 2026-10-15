"""Reject final-name scope, source and terminal-evidence corruptions in memory."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('final_check_lock_negative', HERE / 'review.py')
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
        raise AssertionError('accepted final-name check-lock corruption: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('namespace', 'CheckLockReview'), ('normal_registration', True), ('coverage_added', 5),
                   ('full_acceptance', True), ('roots', []), ('new_sources', []),
                   ('missing_dependency_modules', []), ('results', []), ('definitions', []),
                   ('pure_results', []), ('reference_results', []), ('dependencies', {}),
                   ('commands', {}), ('source_sha256', {}), ('object_sha256', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_elements_check_lock_literal.v', lambda t: t.replace(
    'Theorem elements_check_lock_height_literal_local_spec :',
    'Theorem elements_check_lock_height_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_application_partial_transport.v', lambda t: t.replace(
    'application_jet_partial_spec f ge E A B rep spec2.',
    'application_jet_partial_spec f ge E A B rep spec1.'))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t + '\nsimplicity_check_lock_time WRONG WRONG\n')
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'ast.log', lambda t: t + '\nUNREVIEWED\n')
gate.review()
print(str(rejected) + ' final-C scope/source/bridge/context/command/kernel/AST corruptions rejected')
