"""In-memory caller-support receipt/source corruption tests."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('tapenv_review',Path(__file__).with_name('review.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
w=Path(sys.argv[1]).resolve();gate.review(w)
fixtures=[(w/'REVIEW.json',lambda s:s.replace('"exit_code": 0','"exit_code": 1',1)),
          (w/'REVIEW.json',lambda s:s.replace('"normal_registration": false','"normal_registration": true')),
          (w/'REVIEW.json',lambda s:s.replace('"coverage_added": 0','"coverage_added": 1')),
          (w/'Coq/C/jet_bitcoin_env_tapenv_raw.v',lambda s:s.replace('uint32_array_at m\' bA 8','uint32_array_at m\' bA 16',1)),
          (w/'contracts.log',lambda s:s.replace('TAPENV_TYPE ','MISSING_TYPE ',1)),
          (w/'kernel.log',lambda s:s+'...\n')]
original=Path.read_text
for target,mutate in fixtures:
    target=target.resolve();changed=mutate(original(target))
    if changed==original(target):raise AssertionError('inactive fixture')
    def read(self,*args,**kwargs):return changed if self.resolve()==target else original(self,*args,**kwargs)
    with patch.object(Path,'read_text',read):
        try:gate.review(w)
        except ValueError:pass
        else:raise AssertionError('corrupt builder evidence accepted')
print('Taproot-builder receipt/source corruption fixtures passed: 6')
