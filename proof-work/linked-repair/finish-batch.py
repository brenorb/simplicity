"""Require actual passing corruption fixtures before source-only installation."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('linked_finish', HERE / 'run.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
meta, receipt, _ = gate.review(work)
result = gate.command(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'fixtures', 600)
expected = ('Linked corruption fixtures passed: 16; lexical fixtures passed: 6; '
            'namespace/specification/link-policy checks passed')
if (work / 'fixtures.log').read_text().strip() != expected:
    raise ValueError('incomplete negative-fixture report')
gate.review(work)
tests = {'command': result, 'candidate': str(work), 'source_commit': gate.COMMIT,
         'driver_sha256': gate.old.sha((HERE / 'run.py').read_bytes()),
         'test_driver_sha256': gate.old.sha((HERE / 'test-review.py').read_bytes()),
         'review_sha256': gate.old.sha((work / 'REVIEW.json').read_bytes()),
         'corruption_fixtures': 16, 'lexical_fixtures': 6,
         'namespace_specification_link_policy_checks': True}
gate.old.changed({HERE / meta['group'] / 'TESTS.json': json.dumps(tests, indent=2) + '\n',
                  HERE / meta['group'] / 'fixtures.log': (work / 'fixtures.log').read_text()})
gate.install(work)
