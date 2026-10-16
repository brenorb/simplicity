"""Read-only integration preflight; never invent a positive acceptance.

Exercise premature/unsafe refusals, and reconstruct the real immutable418
history and both reviewed candidate deltas without changing any proof input.
"""
import copy
import importlib.util
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('combined420_install_negative', HERE / 'integration.py')
i = importlib.util.module_from_spec(sp)
sp.loader.exec_module(i)
work = Path(sys.argv[1]).resolve()
before, index = i.s.input_map(), i.s.index_hash()
count = 0


def reject(action, message):
    global count
    try:
        action()
    except ValueError as error:
        assert message in str(error), error
        count += 1
        return
    raise AssertionError('accepted premature/unsafe combined420 installation')


is_file = Path.is_file
def missing_acceptance(self):
    return False if self.name == 'ACCEPTANCE.json' and self.parent in [HERE, work] else is_file(self)

with patch.object(Path, 'is_file', missing_acceptance), patch.object(i.s, 'changed', side_effect=AssertionError('unexpected write')):
    reject(lambda: i.candidate_acceptance(work), 'real full combined420 terminal acceptance')
    reject(lambda: i.install(work), 'real full combined420 terminal acceptance')

# A real controller process, not a lock/receipt, must release the frozen main.
for name in [str(HERE / 'accept.py'), 'proof-work/scalar-lambda-admission/accept.py',
             str(i.g.PRED / 'accept.py'), 'proof-work/elements-null-data-admission/accept.py']:
    result = subprocess.CompletedProcess(['ps'], 0, 'python3 -B ' + name + ' /private/tmp/candidate\n', '')
    with patch.object(i.subprocess, 'run', return_value=result):
        reject(i.controllers_stopped, 'frozen-baseline audit controller is still running')
with patch.object(i.subprocess, 'run', return_value=subprocess.CompletedProcess(['ps'], 0, 'unrelated-process\n', '')):
    i.controllers_stopped()

real_read = i.read
original = real_read(HERE / 'INSTALLATION-PLAN.json')
mutations = [
    ('coverage_before', '419/533'), ('coverage_candidate', '421/533'), ('coverage_added', 1),
    ('source_only_targets', 65), ('main_installation', True), ('full_acceptance', True),
    ('inherited_proof_overwrites', 1), ('compiler_objects_copied', 1),
    ('predecessor419_terminal_required', True),
    ('actual_main418_acceptance_required_before_install', False),
    ('full_combined420_acceptance_required_before_install', False),
    ('targets', original['targets'][:-1]), ('byte_identical_reused_sources', [])]
for key, value in mutations:
    proposal = copy.deepcopy(original)
    proposal[key] = value
    def corrupted_read(path):
        return proposal if path == HERE / 'INSTALLATION-PLAN.json' else real_read(path)
    with patch.object(i, 'read', corrupted_read):
        reject(lambda: i.reviewed_evidence(work), 'wrong combined420 reviewed plan scope')
proposal = copy.deepcopy(original)
proposal['tools_sha256']['accept.py'] = '0' * 64
with patch.object(i, 'read', lambda path: proposal if path == HERE / 'INSTALLATION-PLAN.json' else real_read(path)):
    reject(lambda: i.reviewed_evidence(work), 'reviewed plan/acceptance tool changed')

# Real positive historical validation only; no success evidence is synthesized.
ledger, actual = i.predecessor()
p, historical_before, historical_after = i.reviewed_evidence(work)
assert ledger['coverage'] == '418/533' and actual['actual_main_acceptance'] is True
assert p == original and before == historical_before
assert p['baseline_input_sha256'] == actual['audit_input_sha256']
assert p['baseline_main_acceptance_sha256'] == i.s.sha((i.PRED / 'MAIN-ACCEPTANCE.json').read_bytes())
assert p['baseline_installation_sha256'] == i.s.sha((i.PRED / 'INSTALLATION.json').read_bytes())
assert i.planner.input_map(work) == historical_after
assert i.s.input_map() == before and i.s.index_hash() == index
assert not (HERE / 'INSTALLATION.json').exists()
print(str(count) + ' premature/live-controller/unsafe-plan cases rejected; real418 history and combined420 reviews checked; no installation; main/index unchanged')
