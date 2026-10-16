"""Read-only combined443 source-plan and pending-terminal boundary tests."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal443_plan_negative', HERE / 'prepare-integration.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s, g = p.s, p.g
work = Path(sys.argv[1]).resolve()
before, index = s.input_map(), s.index_hash()
fp = s.inputs.fingerprint(work / 'Coq', work)
recorded = json.loads((HERE / 'INSTALLATION-PLAN.json').read_text())
if p.plan(work) != recorded:
    raise ValueError('recorded combined443 source plan differs')
count = 0


def reject(action):
    global count
    try:
        action()
    except (ValueError, KeyError):
        count += 1
        return
    raise AssertionError('accepted invalid combined443 source-plan boundary')


for candidate in [s.REPO, s.REPO / 'Coq', g.BASE_TREE, g.PROOF_TREE]:
    reject(lambda candidate=candidate: p.plan(candidate))
for name in ['/private/tmp/not-a-source.v', '../escape.v', 'C/not-a-source.vo',
             'C/not-a-source.vos', 'C/not-a-source.vok', 'C/not-a-source.glob', g.METADATA[0]]:
    with patch.object(g, 'NEW_SOURCES', [name] + g.NEW_SOURCES[1:]):
        reject(p.targets)
with patch.object(g, 'NEW_SOURCES', []):
    reject(p.targets)

# Model only a missing real terminal, never a fictitious successful one.
required = g.PRED / 'ACCEPTANCE.json'
is_file = Path.is_file
with patch.object(Path, 'is_file', lambda self: False if self == required else is_file(self)):
    reject(lambda: p.a.prerequisites(work))
if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
    raise AssertionError('these prelaunch tests must run before a normal443 audit')
if (s.input_map() != before or s.index_hash() != index or
    s.inputs.fingerprint(work / 'Coq', work) != fp):
    raise ValueError('read-only source-plan tests changed main/index/private input')
print(str(count) + ' combined443 wrong-tree/escaping/object/duplicate/scope/pending-terminal cases rejected; exact25-target source plan unchanged')
