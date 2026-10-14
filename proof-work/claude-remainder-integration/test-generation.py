"""Generation provenance is not semantic or kernel admission."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('generation_gate', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review_generation()
target = gate.HERE / 'generation/REVIEW.json'


def mutate(text, field, value):
    data = json.loads(text)
    if field == 'exit_code':
        data['generation']['exit_code'] = value
    elif field == 'inputs':
        data['inputs'].pop(next(iter(data['inputs'])))
    else:
        data[field] = value
    return json.dumps(data)


for field, value in [('kind', 'full proof audit'), ('normal_registration', True),
                     ('coverage_added', 1), ('canonical_source_review', 'complete'),
                     ('exit_code', 1), ('inputs', None)]:
    original = Path.read_text
    corrupt = mutate(original(target), field, value)
    def read(self, *args, **kwargs):
        return corrupt if self.resolve() == target.resolve() else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.review_generation()
        except ValueError:
            pass
        else:
            raise AssertionError('generation evidence incorrectly admitted: ' + field)
print('Generation scope/terminal/inventory corruption fixtures passed: 6')
