"""Bounded checked-linking experiments. Never writes into main's Coq tree."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location('linked_remainder', HERE.parent / 'claude-remainder-integration/run.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
coq = work / 'Coq'
changes = {coq / 'C/jets_unlinked.v': (REPO / 'Coq/C/jets.v').read_text(),
           coq / 'C/memcpy_exact.v': gate.blob('Coq/C/memcpy_exact.v').decode(),
           work / 'gen-jets.py': gate.blob('Coq/linked/gen-jets.py').decode()}
original = gate.blob('Coq/linked/C/jet_linked_program.v').decode()
prefix = original[:original.index('Lemma ast_link_main')]
start = prefix.index('Proof.')
prefix = prefix[:start] + 'Proof. timeout 10 (vm_compute; reflexivity). Qed.\n'
gate.safe_source(prefix, 'checked equality probe')
changes[coq / 'C/probe.v'] = prefix
gate.changed(changes)
shutil.copy2(REPO / 'Coq/build-jets.sh', coq / 'build-jets.sh')
subprocess.run([sys.executable, '-B', str(work / 'gen-jets.py'), str(coq / 'C/jets_unlinked.v'),
                str(coq / 'C/memcpy_exact.v'), str(coq / 'C/jets.v')], check=True)
records = {}
for name in ['jets_unlinked', 'memcpy_exact', 'jets', 'probe']:
    command = ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + name + '.v']
    with (work / (name + '.log')).open('wb') as log:
        try:
            result = subprocess.run(command, cwd=coq, env=gate.ENV, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=45)
            code = result.returncode
        except subprocess.TimeoutExpired:
            code = 'deadline'
    records[name] = {'command': command, 'exit_code': code}
    print(name, code, flush=True)
    gate.changed({work / 'EXPERIMENT.json': json.dumps(records, indent=2) + '\n'})
    if code != 0:
        sys.exit(1)
