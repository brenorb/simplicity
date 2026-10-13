"""In-memory tests of the historical-baseline plus additive-support check."""
import contextlib
import importlib.util
import io
from pathlib import Path
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('startup_post_test', Path(__file__).with_name('post-check.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
with contextlib.redirect_stdout(io.StringIO()): gate.check()
repo = gate.gate.stage.REPO
fixtures = [
    (repo / 'Coq/C/jet_sha_startup_state.v', 'read_text', lambda s: s + '\n'),
    (repo / 'C/jets.c', 'read_bytes', lambda s: s + b'\n'),
    (repo / 'Coq/C/jet_public_theorems.txt', 'read_bytes', lambda s: s + b'\n'),
]
for target, method, mutate in fixtures:
    target = target.resolve(); original = getattr(Path, method); changed = mutate(original(target))
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target else original(self, *args, **kwargs)
    with patch.object(Path, method, read):
        try:
            with contextlib.redirect_stdout(io.StringIO()): gate.check()
        except ValueError: pass
        else: raise AssertionError('unreviewed source/metadata delta accepted')
print('Post-integration preservation corruption fixtures passed: 3')
