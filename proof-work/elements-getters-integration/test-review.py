"""In-memory two-getter metadata/deep-record corruption tests."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

spec = importlib.util.spec_from_file_location('getter_review', Path(__file__).with_name('admission.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
c = Path(sys.argv[1]).resolve(); gate.base.review(c)
fixtures = [
    (c/'Coq/C/jet_coverage.tsv', lambda s:s.replace('elements_locktime_local_spec','wrong_spec')),
    (c/'Coq/C/jet_public_theorems.txt', lambda s:s+'C.jet_elements_locktime_local elements_locktime_local_spec\n'),
    (c/'Coq/C/jet_contract_definitions.txt', lambda s:s.replace('elements_locktime_env_rep','other_rep')),
    (c/'Coq/C/jet_contracts.expected', lambda s:s.replace('memcpy_builtin_witness','mutated_witness',1)),
    (c/'Coq/C/jet_assumptions.expected', lambda s:s+'Invented.result : Invented.axiom\n'),
    (c/'new_contracts.out', lambda s:s.replace('VERSION_DEEP_TYPE ','MISSING_TYPE ',1)),
    (c/'new_contracts.out', lambda s:s+'...\n'),
    (c/'KERNEL.json', lambda s:s.replace('"exit_code": 0','"exit_code": 1')),
]
original = Path.read_text
for target, mutate in fixtures:
    target=target.resolve();text=original(target);changed=mutate(text)
    if changed==text:raise AssertionError('inactive fixture')
    def read(self,*args,**kwargs):return changed if self.resolve()==target else original(self,*args,**kwargs)
    with patch.object(Path,'read_text',read):
        try:gate.base.review(c)
        except ValueError:pass
        else:raise AssertionError('corrupt getter preparation accepted')
print('Getter evidence corruption fixtures passed: 8')
