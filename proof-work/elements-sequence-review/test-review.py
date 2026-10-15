"""In-memory sealed sequence proof/evidence corruption fixtures."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sequence_receipt_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
receipt = HERE / 'REVIEW.json'
work = Path(json.loads(receipt.read_text())['candidate'])
original_text, original_bytes = Path.read_text, Path.read_bytes


def reject(path, transform):
    original = original_text(path)
    changed = transform(original)
    assert original != changed
    def text(self, *args, **kwargs):
        return changed if self == path else original_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return changed.encode() if self == path else original_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            gate.review()
        except (ValueError, KeyError):
            return
        raise AssertionError('accepted corrupt sequence evidence: ' + str(path))


def field(key, value):
    def change(text):
        data = json.loads(text)
        data[key] = value
        return json.dumps(data)
    return change


for key, value in [('normal_registration', True), ('coverage_added', 1), ('results', []),
                   ('definitions', []), ('dependencies', {}), ('source_sha256', 'bad')]:
    reject(receipt, field(key, value))
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(work / 'kernel.log', lambda t: t + '\nALTERED\n')
reject(HERE / 'source/jet_elements_sequence_literal.v.source', lambda t: t.replace('544 248 0 696', '544 256 0 696'))
def unsafe(text):
    data = json.loads(text)
    data['commands']['kernel']['command'].append('-norec')
    return json.dumps(data)
reject(receipt, unsafe)
gate.review()
print('10 sequence proof/inventory/source/command/evidence corruptions rejected')
