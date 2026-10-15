"""Test missing-predecessor refusal without launching any acceptance process."""
import importlib.util
from pathlib import Path
import runpy
import subprocess
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('optional_start_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
work = Path(sys.argv[1]).resolve()
before, index = s.input_map(), s.index_hash()
missing = HERE.parent / 'elements-digest-getters-admission/ACCEPTANCE.json'
exists = Path.exists


def fake_exists(self):
    return False if self == missing else exists(self)


def no_mutation(*args, **kwargs):
    raise AssertionError('missing-predecessor refusal attempted a mutation or subprocess')


with patch.object(Path, 'exists', fake_exists), patch.object(Path, 'write_text', no_mutation), \
        patch.object(Path, 'write_bytes', no_mutation), patch.object(subprocess, 'run', no_mutation), \
        patch.object(sys, 'argv', [str(HERE / 'accept.py'), str(work)]):
    try:
        runpy.run_path(str(HERE / 'accept.py'), run_name='__main__')
    except ValueError as error:
        if 'predecessor full acceptance and guarded source installation must complete' not in str(error):
            raise
    else:
        raise AssertionError('missing predecessor did not prevent acceptance launch')
if s.input_map() != before or s.index_hash() != index:
    raise ValueError('start-guard test changed main/index')
print('Missing real 386 acceptance prevents launch; no process, audit or main/index change')
