"""One bounded checked-conversion diagnostic; never edits main secp sources."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('secp_probe_gate', HERE / 'run.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
source = gate.REPO / 'Coq/C/jet_secp_fe_nv.v'
raw = source.read_text()
prefix = raw[:raw.index('Definition nvz_list')]
old = 'Proof. vm_cast_no_check (eq_refl (Some (RIf nv_c (RDone nv_a ONormal) (RDone nv_b ONormal)))). Qed.'
if prefix.count(old) != 1:
    raise ValueError('unexpected normalization equality source')
prefix = prefix.replace(old, 'Proof. timeout 10 (vm_compute; reflexivity). Qed.')
prefix = prefix.replace('Set Default Timeout 600.', 'Set Default Timeout 10.')
prefix += '\nPrint Assumptions nv_run_eq.\n'
gate.old.safe_source(prefix, 'isolated secp normalization probe')
work = Path(tempfile.mkdtemp(prefix='jet-secp-nv-probe.', dir='/tmp')).resolve()
target = work / 'nv_probe.v'
gate.old.changed({target: prefix})
command = ['bash', 'build-jets.sh', '--coqc', '-Q', str(work), 'SecpProbe', '-q', str(target)]
with (work / 'probe.log').open('wb') as log:
    try:
        result = subprocess.run(command, cwd=gate.REPO / 'Coq', env=gate.old.ENV,
                                stdout=log, stderr=subprocess.STDOUT, timeout=45)
        code = result.returncode
    except subprocess.TimeoutExpired:
        code = 'deadline'
if source.read_text() != raw:
    raise ValueError('main secp source changed during diagnostic')
receipt = {'candidate': str(work), 'kind': 'isolated equality diagnostic, not integration',
           'original_source_sha256': gate.old.sha(raw.encode()), 'command': command,
           'exit_code': code, 'log_sha256': gate.old.sha((work / 'probe.log').read_bytes())}
gate.json_write(work / 'PROBE.json', receipt)
gate.json_write(HERE / 'secp-probe/PROBE.json', receipt)
gate.old.changed({HERE / 'secp-probe/nv_probe.v.source': prefix,
                  HERE / 'secp-probe/probe.log': (work / 'probe.log').read_text()})
print(json.dumps(receipt, indent=2))
print((work / 'probe.log').read_text())
