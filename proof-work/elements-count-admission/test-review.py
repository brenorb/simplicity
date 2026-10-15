"""In-memory registration/snapshot/evidence corruptions; never compile them."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_registry_negative', HERE / 'review.py')
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
        raise AssertionError('accepted admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        data = json.loads(text)
        data[key] = value
        return json.dumps(data)
    return change


assembly = work / 'ASSEMBLY.json'
for key, value in [('coverage_added', 100), ('coverage_additions', ''), ('extensions', {}), ('full_acceptance', True)]:
    reject(assembly, field(key, value))
receipt = work / 'PREPARATION.json'
for key, value in [('fresh_compiles', {}), ('new_dependencies', {}), ('new_objects_sha256', {}), ('full_acceptance', True)]:
    reject(receipt, field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('simplicity_num_inputs C.jet_elements_count_local', 'simplicity_num_inputs C.jet_elements_count_payload'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('"simplicity_num_outputs"}', '"simplicity_num_outputs", "simplicity_output_asset"}'))
reject(work / 'Coq/check-jets.sh', lambda t: t.replace('python3 elements-count-review/check-source.py', '# python3 elements-count-review/check-source.py'))
reject(work / 'Coq/C/jet_elements_count_local.v', lambda t: t.replace('Theorem elements_num_inputs_local_spec :', 'Theorem elements_num_inputs_local_spec : False ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
gate.review(work)
print('16 count admission/inventory/source/evidence corruptions rejected')
