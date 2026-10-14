"""In-memory checks that only exact reviewed caller additions are tolerated."""
import contextlib
import importlib.util
import io
from pathlib import Path
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('tapenv_post_test',Path(__file__).with_name('post-check.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
with contextlib.redirect_stdout(io.StringIO()):gate.check()
repo=gate.gate.stage.REPO
fixtures=[(repo/'Coq/bitcoin-env/C/jet_bitcoin_env_tapenv_raw.v','read_text'),
          (repo/'C/bitcoin/env.c','read_bytes'),(repo/'Coq/C/jet_public_theorems.txt','read_bytes')]
for target,method in fixtures:
    target=target.resolve();original=getattr(Path,method);old=original(target)
    changed=old+('\n' if isinstance(old,str) else b'\n')
    def read(self,*args,**kwargs):return changed if self.resolve()==target else original(self,*args,**kwargs)
    with patch.object(Path,method,read):
        try:
            with contextlib.redirect_stdout(io.StringIO()):gate.check()
        except ValueError:pass
        else:raise AssertionError('unreviewed caller/source/registry mutation accepted')
print('Post-import caller preservation corruption fixtures passed: 3')
