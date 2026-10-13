"""Read-only corruption fixtures for the SHA supporting-proof receipt."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('startup_fixture_review', Path(__file__).with_name('review.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
candidate = Path(sys.argv[1]).resolve()
gate.review(candidate)
original = Path.read_text
fixtures = [
    (candidate / 'ASSEMBLY.json', lambda s: s.replace('"namespace_only_transport": true', '"namespace_only_transport": false')),
    (candidate / 'REVIEW.json', lambda s: s.replace('"normal_registry_admission": false', '"normal_registry_admission": true')),
    (candidate / 'REVIEW.json', lambda s: s.replace('"exit_code": 0', '"exit_code": 1', 1)),
    (candidate / 'REVIEW.json', lambda s: s.replace('"coverage_added": 0', '"coverage_added": 1')),
    (candidate / 'Coq/C/jet_sha_startup_state.v', lambda s: s.replace('64 < count', '0 < count', 1)),
    (candidate / 'contracts.out', lambda s: s.replace('SHA_STARTUP_TYPE ', 'MISSING_TYPE ', 1)),
]
for target, corrupt in fixtures:
    target = target.resolve(); text = original(target); changed = corrupt(text)
    if changed == text: raise AssertionError('inactive fixture')
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try: gate.review(candidate)
        except ValueError: pass
        else: raise AssertionError('SHA corruption accepted: ' + str(target))
print('SHA startup evidence/source corruption fixtures passed: 6')
