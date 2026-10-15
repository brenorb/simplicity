"""In-memory admission corruptions only; never compile invalid proofs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sequence_registry_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes


def reject(path, transform):
    original = read_text(path)
    altered = transform(original)
    assert original != altered
    def text(self, *args, **kwargs):
        return altered if self == path else read_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return altered.encode() if self == path else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            gate.review(work)
        except (ValueError, KeyError):
            return
        raise AssertionError('accepted sequence admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [('coverage_added', 100), ('coverage_additions', ''), ('extensions', {}),
                   ('new_sources', []), ('full_acceptance', True)]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('fresh_compiles', {}), ('new_dependencies', {}), ('new_objects_sha256', {}), ('full_acceptance', True)]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('simplicity_input_sequence C.jet_elements_indexed_scalar_jets',
                                                         'simplicity_input_sequence C.jet_elements_current_jets'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('"simplicity_current_sequence"}',
                                                       '"simplicity_current_sequence", "simplicity_output_asset"}'))
reject(work / 'Coq/check-jets.sh', lambda t: t.replace('python3 elements-sequence-review/check-source.py',
                                                     '# python3 elements-sequence-review/check-source.py'))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_elements_sequence_literal.v', lambda t: t.replace(
    'Theorem elements_input_sequence_literal_local_spec :', 'Theorem elements_input_sequence_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
gate.review(work)
print('18 sequence admission/source/printer/snapshot/terminal evidence corruptions rejected')
