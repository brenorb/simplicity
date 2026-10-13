"""In-memory evidence corruption tests; no temporary fake proofs are compiled."""
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('version_admission_review', Path(__file__).with_name('admission.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)


def reject(candidate, path, corrupt):
    original = Path.read_text
    target = path.resolve()
    text = original(target)
    changed = corrupt(text)
    if changed == text:
        raise AssertionError('inactive mutation')
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target else original(self, *args, **kwargs)
    Path.read_text = read
    try:
        try:
            gate.review(candidate)
        except ValueError:
            pass
        else:
            raise AssertionError('corrupt evidence accepted')
    finally:
        Path.read_text = original


candidate = Path(sys.argv[1]).resolve()
gate.review(candidate)
coq = candidate / 'Coq'
reject(candidate, coq / 'C/jet_coverage.tsv', lambda s: s.replace('elements_version_local_spec', 'wrong_version_spec'))
reject(candidate, coq / 'C/jet_public_theorems.txt', lambda s: s + 'C.jet_elements_version_local elements_version_local_spec\n')
reject(candidate, coq / 'C/jet_contract_definitions.txt', lambda s: s.replace('Elements.sem', 'Elements.wrong_sem'))
reject(candidate, coq / 'C/jet_contracts.expected', lambda s: s.replace('memcpy_builtin_witness', 'mutated_memcpy_builtin_witness', 1))
reject(candidate, coq / 'C/jet_assumptions.expected', lambda s: s + 'Invented.result : Invented.axiom\n')
reject(candidate, coq / 'C/jet_assumptions.expected', lambda s: s + s.splitlines()[0] + '\n')
reject(candidate, candidate / 'new_contracts.out', lambda s: s.replace('VERSION_DEEP_TYPE ', 'MISSING_DEEP_TYPE ', 1))
reject(candidate, candidate / 'new_contracts.out', lambda s: s + '...\n')
print('Version admission evidence corruption fixtures passed: 8')
