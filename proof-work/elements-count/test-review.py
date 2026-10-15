"""Reject altered count proof receipts/artifacts without editing any file."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
s = importlib.util.spec_from_file_location('count_review_tests', HERE / 'review.py')
gate = importlib.util.module_from_spec(s)
s.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.validate(work)
raw_text, raw_bytes = Path.read_text, Path.read_bytes


def mutation(path, transform):
    before = raw_text(path)
    after = transform(before)
    assert after != before
    def text(self, *args, **kwargs):
        return after if self == path else raw_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return after.encode() if self == path else raw_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            gate.validate(work)
        except (ValueError, KeyError):
            return
        raise AssertionError('accepted receipt/artifact corruption: ' + str(path))


def change(key, value):
    def f(text):
        data = json.loads(text)
        data[key] = value
        return json.dumps(data)
    return f


receipt = work / 'REVIEW.json'
for key, value in [('normal_registration', True), ('coverage_added', 2), ('assembly_sha256', 'bad'),
                   ('results', []), ('dependencies', {}), ('evidence_sha256', {})]:
    mutation(receipt, change(key, value))
mutation(work / 'ASSEMBLY.json', change('roots', []))
mutation(work / 'ASSEMBLY.json', change('modules', []))
for key in ['build', 'kernel', 'AST']:
    def bad(text, key=key):
        data = json.loads(text)
        data[key]['exit_code'] = 1
        return json.dumps(data)
    mutation(receipt, bad)
def unsafe(text):
    data = json.loads(text)
    data['kernel']['command'].append('-norec')
    return json.dumps(data)
mutation(receipt, unsafe)
mutation(work / 'contracts.log', lambda t: t + '\n...\n')
mutation(work / 'kernel.log', lambda t: t + '\nCORRUPTION\n')
mutation(work / 'Coq/C/jet_elements_count_payload.v', lambda t: t + '\n(* changed source *)\n')
mutation(work / 'Coq/Simplicity/Word.v', lambda t: t + '\n(* changed canonical source *)\n')
gate.validate(work)
print('16 count receipt/artifact corruptions rejected')
