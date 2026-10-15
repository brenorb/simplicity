"""Corrupt receipts in memory only; reject weak or mismatched proof evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('finality_negative_review', HERE / 'review.py')
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
        raise AssertionError('accepted finality evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('coverage_added', 1), ('normal_registration', True), ('full_acceptance', True),
                   ('roots', []), ('fresh_modules', []), ('results', []), ('definitions', []),
                   ('dependencies', {}), ('commands', {}), ('sources_sha256', {}),
                   ('objects_sha256', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
reject(HERE / 'AST.json', field('exit_code', 1))
reject(HERE / 'AST.json', field('command', ['true']))
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'source-negative.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_elements_is_final_local.v', lambda t: t.replace(
    'Theorem elements_tx_is_final_local_spec :', 'Theorem elements_tx_is_final_local_spec : False ->'))
reject(HERE / 'source/jet_elements_is_final_spec.v.source', lambda t: t.replace(
    'for_while_program 5 (final_body op)', 'for_while_program 4 (final_body op)'))
gate.review()
print(str(count) + ' finality scope/source/command/snapshot/kernel/AST evidence corruptions rejected')
