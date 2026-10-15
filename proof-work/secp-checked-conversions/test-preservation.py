"""Reject unreviewed changes to the explicit existing-source repair overlay."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('repair_preservation_tests', HERE / 'preservation.py')
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
changes = policy.transformations(REPO)
expected = {p: policy.sha(before.encode()) for p, (before, _) in changes.items()}
actual = policy.apply_reviewed_repairs(expected, REPO)
assert actual == {p: policy.sha(after.encode()) for p, (_, after) in changes.items()}
ledger = HERE / 'INSTALLATION.json'
raw = Path.read_text


def rejected(transform):
    altered = transform(json.loads(raw(ledger)))
    def text(self, *args, **kwargs):
        return json.dumps(altered) if self == ledger else raw(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text):
        try:
            policy.apply_reviewed_repairs(expected, REPO)
        except (ValueError, KeyError):
            return
        raise AssertionError('accepted corrupted repair ledger')


def field(key, value):
    def change(data):
        data[key] = value
        return data
    return change


original = json.loads(raw(ledger))
rejected(field('base_commit', 'bad'))
rejected(field('repairs', {}))
rejected(field('repairs', {**original['repairs'], 'Coq/C/not_reviewed.v': {}}))
for key in ['before_sha256', 'after_sha256']:
    def change(data, key=key):
        data['repairs']['Coq/C/jet_secp_fe_nv.v'][key] = 'bad'
        return data
    rejected(change)
for name in expected:
    bad = dict(expected, **{name: 'bad'})
    try:
        policy.apply_reviewed_repairs(bad, REPO)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted mismatched original baseline: ' + name)
name = REPO / 'Coq/C/jet_secp_fe_nv.v'
def text(self, *args, **kwargs):
    return changes[str(name.relative_to(REPO))][0] if self == name else raw(self, *args, **kwargs)
with patch.object(Path, 'read_text', text):
    try:
        policy.apply_reviewed_repairs(expected, REPO)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted unchecked proof regression')
print('11 explicit repair-preservation corruptions rejected')

# The linked audit keeps its original driver digest. Only the exact new
# preservation-hook/provenance-hook delta may explain that historical pin.
driver = REPO / 'proof-work/linked-repair/run.py'
historical = policy.subprocess.check_output(['git', 'show', policy.BASE + ':proof-work/linked-repair/run.py'], cwd=REPO)
assert policy.linked_driver_matches(policy.sha(historical), REPO)
assert policy.linked_driver_matches(policy.sha(driver.read_bytes()), REPO)
assert not policy.linked_driver_matches('bad', REPO)
raw_bytes = Path.read_bytes
for altered in [driver.read_bytes() + b'\n# unknown edit\n',
                driver.read_bytes().replace(b"raise ValueError('receipt scope/driver drift')", b'pass')]:
    def binary(self, *args, **kwargs):
        return altered if self == driver else raw_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_bytes', binary):
        assert not policy.linked_driver_matches(policy.sha(historical), REPO)
extra = json.loads((HERE / 'EXTRA_REVIEW.json').read_text())
assert policy.sha((HERE / 'historical-tools/preservation.py.source').read_bytes()) == extra['tool_sha256']['preservation.py']
print('Historical driver provenance pinned; unknown hash, extra edit and removed check rejected')
