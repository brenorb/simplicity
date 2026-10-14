"""Preservation rejects edits outside the exact imported transaction batch."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('tx_post_gate', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(json.loads((gate.HERE / 'ASSEMBLY.json').read_text())['candidate'])
gate.preservation(work, installed=True)
for target in [gate.REPO / 'Coq/bitcoin-env/C/jet_bitcoin_env_tx_raw.v',
               gate.REPO / 'C/bitcoin/env.c', gate.REPO / 'Coq/C/jet_coverage.tsv']:
    original = Path.read_bytes
    changed = original(target) + b'\ncorruption\n'
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target.resolve() else original(self, *args, **kwargs)
    # Imported files are checked by read_text; fingerprint catches all via bytes.
    original_text = Path.read_text
    def read_text(self, *args, **kwargs):
        return changed.decode() if self.resolve() == target.resolve() else original_text(self, *args, **kwargs)
    with patch.object(Path, 'read_bytes', read), patch.object(Path, 'read_text', read_text):
        try:
            gate.preservation(work, installed=True)
        except ValueError:
            pass
        else:
            raise AssertionError('outside/imported source edit accepted')
print('Transaction post-import preservation corruption fixtures passed: 3')
