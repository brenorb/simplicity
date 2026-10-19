"""Read-only validation of the completed negative diagnostic receipt."""
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('checked_frozen_identity', HERE / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
work, extra = v.bound()
r = json.loads((HERE / 'CHECKED.json').read_text())
expected_command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' +
    ' '.join(extra + [v.ROOT])]
log = (HERE / 'identity-kernel.log').read_bytes()
if (not r['recursive_kernel_check'] or not r['all_three_theorems_closed'] or
        r['run_sha256'] != v.s.sha((HERE / 'RUN.json').read_bytes()) or
        r['kernel']['command'] != expected_command or r['kernel']['exit_code'] or
        r['kernel']['log_sha256'] != v.s.sha(log) or log != (work / 'identity-kernel.log').read_bytes()):
    raise ValueError('completed diagnostic/kernel evidence differs')
allowlist = set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
if not set(r['inherited_library_axiom_subset']) <= allowlist:
    raise ValueError('diagnostic introduces a non-inherited library axiom')
v.s.kernel.kernel(log.decode(), r['inherited_library_axiom_subset'])
print('Three closed frozen-target identity counterexample proofs and recursive kernel evidence verified')
