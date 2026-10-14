"""Post-import preservation must reject imported, production or registry edits."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('composition_post_test', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(json.loads((gate.HERE / 'ASSEMBLY.json').read_text())['candidate'])
gate.current.preservation(work, installed=True)
for target in [gate.REPO / 'Coq/bitcoin-env/C/jet_bitcoin_env_build.v',
               gate.REPO / 'C/bitcoin/txEnv.c', gate.REPO / 'Coq/C/jet_coverage.tsv']:
    original = Path.read_bytes
    original_text = Path.read_text
    changed = original(target) + b'\ncorruption\n'
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target.resolve() else original(self, *args, **kwargs)
    def read_text(self, *args, **kwargs):
        return changed.decode() if self.resolve() == target.resolve() else original_text(self, *args, **kwargs)
    with patch.object(Path, 'read_bytes', read), patch.object(Path, 'read_text', read_text):
        try:
            gate.current.preservation(work, installed=True)
        except ValueError:
            pass
        else:
            raise AssertionError('changed composition/production/registry source accepted')
print('Composition post-import preservation corruption fixtures passed: 3')
