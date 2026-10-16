"""Read-only unsafe combined420 target / missing-review rejection tests."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('combined420_plan_negative', HERE / 'prepare-integration.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
work = Path(sys.argv[1]).resolve()
before, index = p.s.input_map(), p.s.index_hash()
count = 0


def reject(action, message):
    global count
    try:
        action()
    except ValueError as error:
        assert message in str(error), error
        count += 1
        return
    raise AssertionError('accepted unsafe/unreviewed combined source plan')


assert len(p.targets()) == 66
reject(lambda: p.plan(p.s.REPO), 'distinct private combined candidate')
reject(lambda: p.plan(p.s.REPO / 'proof-work'), 'distinct private combined candidate')
for n in ['/private/tmp/outside.v', '../outside.v', 'C/compiled.vo', 'C/compiled.vos', 'C/compiled.vok', 'C/compiled.glob']:
    with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1] + [n]):
        reject(p.targets, 'escaping or non-source integration target')
with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1]):
    reject(p.targets, 'wrong combined420 additive target inventory')
with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1] + [p.g.NEW_SOURCES[0]]):
    reject(p.targets, 'wrong combined420 additive target inventory')
with patch.object(p.g, 'REUSED_SOURCES', []):
    reject(p.targets, 'wrong combined420 additive target inventory')
is_file = Path.is_file
def missing_review(self):
    return False if self == HERE / 'REVIEW.json' else is_file(self)
with patch.object(Path, 'is_file', missing_review):
    reject(lambda: p.plan(work), 'completed normal420 review required')
if p.s.input_map() != before or p.s.index_hash() != index:
    raise ValueError('read-only plan tests changed main/index')
print(str(count) + ' unsafe/unreviewed combined420 target plans rejected; main/index unchanged')
