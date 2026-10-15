"""Check only the missing canonical source/AST obligations, without rewriting history."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_source_preparation', HERE / 'review-source.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
s = review.s
review.checkpoint.review()
if (HERE / 'PREPARATION.json').exists():
    raise ValueError('source preparation already completed; inspect existing evidence')
checked = json.loads((HERE / 'CHECKED.json').read_text())
work = Path(checked['candidate'])
commands = {n: s.run(work, cmd, n, 300) for n, cmd in review.commands(work).items()}
review.checkpoint.review()
gate = review.load('indexed_source_preparation_gate', HERE / 'check-source.py')
record = {'candidate': str(work), 'candidate_input_sha256': checked['candidate_input_sha256'],
          'checkpoint_sha256': s.sha((HERE / 'CHECKED.json').read_bytes()),
          'checkpoint_review_sha256': s.sha((HERE / 'EVIDENCE-REVIEW.json').read_bytes()),
          'commands': commands, 'tools_sha256': {n: s.sha((HERE / n).read_bytes()) for n in review.TOOLS},
          'source_correspondence': gate.check(work, work / 'Coq', work / 'Coq/C/jet_elements_indexed_literal.v'),
          'canonical_source_review_complete': True, 'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for n in commands:
    changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
s.changed(changes)
print(json.dumps(review.review(), indent=2))
