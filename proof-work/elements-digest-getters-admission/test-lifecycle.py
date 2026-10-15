"""Reject premature/repeated integration without modifying main or staging.

This tests the early guards, not a successful installation. Positive installation
and source identity checks must run only after both real terminal acceptances.
"""
import importlib.util
import json
from pathlib import Path
import runpy
import subprocess
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('digest_lifecycle_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
work = Path(json.loads((HERE / 'ASSEMBLY.json').read_text())['candidate'])
before, index = s.input_map(), s.index_hash()
exists = Path.exists
prior = HERE.parent / 'elements-timelock-pegin-admission/MAIN-ACCEPTANCE.json'


def no_mutation(*args, **kwargs):
    raise AssertionError('early lifecycle guard attempted a mutation or subprocess')


cases = [
    ({HERE / 'INSTALLATION.json': True}, 'one-time eight-getter installation already performed'),
    ({HERE / 'INSTALLATION.json': False, work / 'ACCEPTANCE.json': False}, 'full eight-getter acceptance has not terminated successfully'),
    ({HERE / 'INSTALLATION.json': False, work / 'ACCEPTANCE.json': True, prior: False}, 'prerequisite actual-main getter acceptance is not complete'),
]
for overrides, message in cases:
    def fake_exists(self):
        return overrides[self] if self in overrides else exists(self)
    with patch.object(Path, 'exists', fake_exists), patch.object(Path, 'write_text', no_mutation), \
            patch.object(Path, 'write_bytes', no_mutation), patch.object(subprocess, 'run', no_mutation), \
            patch.object(sys, 'argv', [str(HERE / 'install.py'), str(work)]):
        try:
            runpy.run_path(str(HERE / 'install.py'), run_name='__main__')
        except ValueError as error:
            if message not in str(error):
                raise
        else:
            raise AssertionError('premature integration guard failed: ' + message)
for name in ['install.py', 'post-check.py', 'main-accept.py']:
    compile((HERE / name).read_text(), str(HERE / name), 'exec')
if s.input_map() != before or s.index_hash() != index:
    raise ValueError('lifecycle testing changed main/staging')
print('3 early installation guards reject repeated/missing isolated/missing actual-main acceptance; main/index unchanged; positive installation not claimed')
