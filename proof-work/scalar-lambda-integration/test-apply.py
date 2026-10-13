"""Reject nonterminal/mismatched acceptance without any main/candidate writes."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('lambda_apply_negative', archive / 'apply-main.py')
module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
assembly = json.loads((archive / 'ASSEMBLY.json').read_text())
candidate = (Path(assembly['candidate']) / 'Coq').resolve()
receipt_path = archive / 'ACCEPTANCE.json'
original = Path.read_text
before = module.planner.main_state()
fixtures = [
    {'exit_code': None, 'post_run_snapshot_review_passed': True, 'candidate': assembly['candidate']},
    {'exit_code': 1, 'post_run_snapshot_review_passed': True, 'candidate': assembly['candidate']},
    {'exit_code': 0, 'post_run_snapshot_review_passed': False, 'candidate': assembly['candidate']},
    {'exit_code': 0, 'post_run_snapshot_review_passed': True, 'candidate': '/tmp/wrong-candidate'},
]
for data in fixtures:
    def read(path, *args, **kwargs):
        return json.dumps(data) if path == receipt_path else original(path, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            module.acceptance(candidate)
        except ValueError:
            pass
        else:
            raise AssertionError('nonterminal/mismatched acceptance accepted')
if before != module.planner.main_state():
    raise AssertionError('acceptance guard test altered main/index')
print('4 nonterminal/mismatched acceptance fixtures rejected; main and index unchanged')

