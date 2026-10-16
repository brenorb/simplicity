"""Read-only premature/unsafe installation-plan rejection tests.

No successful acceptance receipt is fabricated and no plan is recorded.
"""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('null_data_plan_negative', HERE / 'prepare-integration.py')
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
    raise AssertionError('accepted unsafe/premature integration plan')


assert len(p.targets()) == 38
assert len(p.g.NEW_SOURCES) == 24 and len(p.g.GUARDS) == 3
reject(lambda: p.plan(p.s.REPO), 'distinct private source tree')
reject(lambda: p.plan(p.s.REPO / 'proof-work'), 'distinct private source tree')
for unsafe in ['/private/tmp/arbitrary.v', '../outside.v', 'C/compiled.vo', 'C/compiled.vos',
               'C/compiled.vok', 'C/compiled.glob', 'C/not_source.bin']:
    with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1] + [unsafe]):
        reject(p.targets, 'unsafe/non-source integration target')
with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1]):
    reject(p.targets, 'wrong source-only419 target inventory')
with patch.object(p.g, 'NEW_SOURCES', p.g.NEW_SOURCES[:-1] + [p.g.NEW_SOURCES[0]]):
    reject(p.targets, 'wrong source-only419 target inventory')
if not (HERE / 'ACCEPTANCE.json').exists():
    reject(lambda: p.plan(work), 'full isolated419 acceptance required')
else:
    # Once real acceptance exists, test its absence without altering it.
    exists = Path.exists
    def absent(self):
        return False if self == HERE / 'ACCEPTANCE.json' else exists(self)
    with patch.object(Path, 'exists', absent):
        reject(lambda: p.plan(work), 'full isolated419 acceptance required')
if p.s.input_map() != before or p.s.index_hash() != index:
    raise ValueError('read-only installation-plan tests changed main/index')
print(str(count) + ' premature/unsafe source-only integration plans rejected; main/index unchanged')
