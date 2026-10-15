"""Reject checkpoint promotion, incomplete evidence and source/object drift in memory."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_checkpoint_negative', HERE / 'review.py')
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
    assert altered != original, path
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
        raise AssertionError('accepted corrupted checkpoint: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('namespace', 'Scratch'), ('canonical_source_review_complete', True),
                   ('normal_registration', True), ('coverage_added', 3), ('full_acceptance', True),
                   ('roots', []), ('new_sources', []), ('fresh_modules', []), ('reused_objects_sha256', {}),
                   ('results', []), ('definitions', []), ('endpoints', []), ('closed_shared_lemmas', []),
                   ('dependencies', {}), ('commands', {}), ('source_sha256', ''), ('object_sha256', ''),
                   ('checkpoint_driver_sha256', ''), ('candidate_input_sha256', ''), ('main_inputs', {})]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(work / 'Coq/C/jet_elements_indexed_literal.v', lambda t: t.replace(
    'Theorem elements_input_prev_outpoint_literal_local_spec :', 'Theorem elements_input_prev_outpoint_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t + '\nsimplicity_input_prev_outpoint WRONG WRONG\n')
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(HERE / 'contracts.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'assumptions.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
gate.review()
print(str(count) + ' checkpoint scope/promotion/source/command/report/kernel corruptions rejected')
