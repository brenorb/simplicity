"""Reject corrupted scope/command/source/dependency receipts in memory."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('negative_current_sequence_review', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
original = json.loads((HERE / 'REVIEW.json').read_text())
gate.review(original)
fixtures = [
    lambda r: r.update(coverage_added=1),
    lambda r: r.update(normal_registration=True),
    lambda r: r.update(source_sha256='0' * 64),
    lambda r: r.update(base_input_sha256='0' * 64),
    lambda r: r.update(coq_input_sha256='0' * 64),
    lambda r: r['commands'].pop('kernel'),
    lambda r: r['commands']['kernel'].update(exit_code=1),
    lambda r: r['commands']['compile']['command'].append('-vos'),
    lambda r: r['commands']['source'].update(log_sha256='0' * 64),
    lambda r: r['evidence_sha256'].update({'Proof/jet_elements_current_sequence_literal.vo': '0' * 64}),
    lambda r: r['evidence_sha256'].pop('Proof/jet_elements_current_sequence_literal.vo'),
    lambda r: r['dependencies'][r['results'][-1]].append('Unproved.execution'),
    lambda r: r['results'].pop(),
    lambda r: r['definitions'].pop(),
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
        raise AssertionError('corrupt evidence accepted')
print(str(len(fixtures)) + ' scope/source/object/assumption/terminal evidence corruptions rejected')
