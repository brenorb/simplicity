"""Read-only receipt mutation checks; no invalid proof is compiled."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('negative_hash_review', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
original = json.loads((HERE / 'REVIEW.json').read_text())
gate.review(original)
fixtures = [
    lambda r: r.update(coverage_added=2),
    lambda r: r.update(normal_registration=True),
    lambda r: r.update(coq_input_sha256='0' * 64),
    lambda r: r['source_sha256'].update(jet_haskell_hash_word='0' * 64),
    lambda r: r['commands'].pop('kernel'),
    lambda r: r['commands']['kernel'].update(exit_code=1),
    lambda r: r['commands']['jet_haskell_hash_word']['command'].append('-vos'),
    lambda r: r['evidence_sha256'].pop('Proof/jet_elements_hash_literal.vo'),
    lambda r: r['dependencies'][r['pure_results'][0]].append('Unproved.decoder'),
    lambda r: r['tools_sha256'].pop('test-source.py'),
]
for corrupt in fixtures:
    altered = copy.deepcopy(original)
    corrupt(altered)
    try:
        gate.review(altered)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted hash proof receipt corruption')
print(str(len(fixtures)) + ' scope/source/object/assumption/terminal corruptions rejected')
