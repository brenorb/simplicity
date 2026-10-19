"""Recheck the actual count jets after one proof-only frozen-bound repair.

The failed normal tree is not edited. A fresh derivative changes only the
output-bound conversion in the bridge, not any target or public theorem type.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('count_frozen_acceptance_state', HERE.parent / 'secp-field-acceptance/run.py')
r = importlib.util.module_from_spec(sp)
sp.loader.exec_module(r)
s = r.s
g = s.load('count_frozen_reports', HERE.parent / 'elements-tap-getters/check.py')
MODULES = ['C.jet_bitcoin_count_bridge', 'C.jet_bitcoin_count_local']


def main():
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('count repair already launched; poll the existing handle')
    base, prior = r.identity()
    terminal = json.loads((HERE.parent / 'secp-field-acceptance/BUILD-PROCESS.json').read_text())
    if not terminal['terminal'] or terminal['exit_code'] != 2:
        raise ValueError('normal build is not the recorded terminal failure')
    repair = json.loads((HERE / 'REPAIR.json').read_text())
    old = (base / repair['original']).read_text()
    new = (HERE / 'Bridge.v.source').read_text()
    before_text, after_text = repair['only_change']['old'], repair['only_change']['new']
    if (s.sha(old.encode()) != repair['old_source_sha256'] or
            s.sha(new.encode()) != repair['new_source_sha256'] or
            old.count(before_text) != 1 or old.replace(before_text, after_text, 1) != new):
        raise ValueError('repair is not exactly the intended one-line proof change')
    before = s.inputs.fingerprint(base / 'Coq', base)
    work = Path(tempfile.mkdtemp(prefix='jet-bitcoin-count-frozen-', dir='/private/tmp'))
    subprocess.run(['cp', '-R', str(base / 'Coq'), str(base / 'C'), str(base / 'Haskell'), str(work)], check=True)
    if s.inputs.fingerprint(work / 'Coq', work) != before:
        raise ValueError('count derivative copy differs')
    s.changed({work / repair['original']: new})
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), parent_candidate=str(base),
        parent_input_sha256=before, input_sha256=fingerprint,
        checker_sha256=s.sha(Path(__file__).read_bytes()), complete=False), indent=2) + '\n'})
    commands, modules = {}, []
    for module in MODULES:
        source = work / 'Coq' / (module.replace('.', '/') + '.v')
        commands[module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(source)],
            'count-fresh-' + source.stem, 60)
        modules.append((module, source))
    results, definitions, deps = g.reports(work, modules, 'count', commands)
    old_profiles = {}
    for line in (base / 'Coq/C/jet_assumptions.expected').read_text().splitlines():
        name, axioms = line.split(' : ', 1)
        old_profiles[name] = set() if axioms == 'closed' else set(axioms.split(', '))
    if len(results) != 10 or len(definitions) != 3 or deps != {n: old_profiles[n] for n in results}:
        raise ValueError('count bridge/getter assumptions differ from the recorded originals')
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet'],
        input='Require C.jet_bitcoin_count_local.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('count loaded closure unavailable')
    local = {}
    for module in re.findall(r'^\s+((?:C|Simplicity|Util)\.[\w.]+)\s*$', query.stdout, re.M):
        name = module.replace('.', '/') + '.v'
        p = work / 'Coq' / name
        local[name] = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o C.jet_bitcoin_count_local']
    kernel = s.run(work, command, 'count-kernel', 900)
    text = (work / 'count-kernel.log').read_text()
    context = sorted(text.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    if not set(context) <= set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()):
        raise ValueError('count proof adds a non-inherited library axiom')
    s.kernel.kernel(text, context)
    r.identity()
    if (s.inputs.fingerprint(base / 'Coq', base) != before or
            s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
        raise ValueError('count/parent inputs changed during verification')
    receipt = dict(candidate=str(work), parent_candidate=str(base), input_sha256=fingerprint,
        parent_input_sha256=before, checker_sha256=s.sha(Path(__file__).read_bytes()),
        repair_sha256=s.sha((HERE / 'REPAIR.json').read_bytes()),
        results=results, definitions=definitions, dependencies={n: sorted(ds) for n, ds in deps.items()},
        commands=commands, kernel=kernel, inherited_library_axiom_subset=context,
        loaded_local_source_objects=local, theorem_statements_unchanged=True,
        only_one_proof_line_changed=True, original_domain_unchanged=True,
        recursive_kernel_check=True, whole_count_jets_rechecked=True,
        full_repository_acceptance=False, coverage_added=0)
    s.changed({HERE / 'CHECKED.json': json.dumps(receipt, indent=2) + '\n',
        HERE / 'count-assumptions.log': (work / 'count-assumptions.log').read_text(),
        HERE / 'count-contracts.log': (work / 'count-contracts.log').read_text(),
        HERE / 'count-kernel.log': text, HERE / 'loaded-libraries.log': query.stdout})
    print('Both complete original Bitcoin count-jet contracts recompiled and kernel-checked; no target changes', flush=True)


if __name__ == '__main__':
    main()
