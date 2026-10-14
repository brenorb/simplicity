"""Wrapper regression: an unchanged metadata update must not invoke apply_patch."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('composition_wrapper_test', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
source = Path(__file__).resolve()
with patch.object(gate, 'original_patch') as apply:
    gate.patch_changed({source: source.read_text()})
    apply.assert_not_called()
    gate.patch_changed({source: source.read_text() + '\n# changed\n'})
    apply.assert_called_once()
print('No-op metadata patch regression passed')
