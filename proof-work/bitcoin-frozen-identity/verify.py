"""Source-bound, closed negative identity diagnostic; no target correction."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('identity_diagnostic_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('identity_diagnostic_reports', HERE.parent / 'elements-tap-getters/check.py')
ROOT = 'FrozenBitcoin.Frozen'


def identity():
    prep = json.loads((HERE.parent / 'secp-field-acceptance/PREPARATION.json').read_text())
    work = Path(prep['candidate'])
    if s.input_map() != prep['main_inputs'] or s.index_hash() != prep['staged_patch_sha256']:
        raise ValueError('checkout inputs/staging changed')
    for name in ['Simplicity/Primitive/Bitcoin.v', 'Simplicity/Primitive.v', 'Simplicity/MerkleRoot.v']:
        original = subprocess.check_output(['git', 'show', '91d89bac:Coq/' + name], cwd=REPO)
        if (work / 'Coq' / name).read_bytes() != original:
            raise ValueError('diagnostic target differs from starting revision: ' + name)
    source = work / 'identity-diagnostic/Frozen.v'
    if source.is_symlink() or source.read_bytes() != (HERE / 'Frozen.v.source').read_bytes():
        raise ValueError('diagnostic source differs')
    s.safe_source(source.read_text(), ROOT)
    return work, source, ['-Q', str(source.parent), 'FrozenBitcoin']


def compile():
    work, source, extra = identity()
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('diagnostic phase already launched; poll original handle')
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(work),
        complete=False, driver_sha256=s.sha(Path(__file__).read_bytes())), indent=2) + '\n'})
    commands = {'compile': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)],
        'identity-compile', 60)}
    results, definitions, deps = g.reports(work, [(ROOT, source)], 'identity', commands, extra)
    if len(results) != 3 or definitions or any(deps.values()):
        raise ValueError('expected three fully closed diagnostic theorems')
    query = 'Require ' + ROOT + '.\nPrint Libraries.\n'
    run = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra], input=query,
        cwd=work / 'Coq', env=s.ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=60)
    if run.returncode or re.search(r'(?m)^(?:Error|Anomaly):', run.stdout):
        raise ValueError('could not inspect diagnostic loaded closure')
    modules = set(re.findall(r'^\s+((?:C|Simplicity|Util)\.[\w.]+)\s*$', run.stdout, re.M))
    if 'Simplicity.Primitive.Bitcoin' not in modules:
        raise ValueError('diagnostic did not load the frozen original model')
    local = {}
    for module in sorted(modules):
        name = module.replace('.', '/') + '.v'
        p = work / 'Coq' / name
        local[name] = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
    receipt = dict(candidate=str(work), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()),
        loaded_local_source_objects=local, driver_sha256=s.sha(Path(__file__).read_bytes()),
        main_inputs=s.input_map(), staged_patch_sha256=s.index_hash(),
        negative_identity_diagnostic=True, c_execution_counterexample=False, target_correction=False)
    s.changed({HERE / 'RUN.json': json.dumps(receipt, indent=2) + '\n',
        HERE / 'identity-assumptions.log': (work / 'identity-assumptions.log').read_text(),
        HERE / 'identity-contracts.log': (work / 'identity-contracts.log').read_text(),
        HERE / 'loaded-libraries.log': run.stdout})
    print('Three closed identity counterexample results freshly compiled', flush=True)


def bound():
    work, source, extra = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['source_sha256'] != s.sha(source.read_bytes()) or
            r['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            any(r['dependencies'].values())):
        raise ValueError('diagnostic compile identity/profile differs')
    for name, row in r['loaded_local_source_objects'].items():
        p = work / 'Coq' / name
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('diagnostic dependency source/object changed: ' + name)
    for name, row in r['commands'].items():
        stem = 'identity-compile' if name == 'compile' else name
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('diagnostic compilation/report log differs')
    return work, extra


def kernel():
    work, extra = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('diagnostic kernel phase already launched; poll original handle')
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=command,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), complete=False), indent=2) + '\n'})
    row = s.run(work, command, 'identity-kernel', 600)
    text = (work / 'identity-kernel.log').read_text()
    context = sorted(text.split('* Axioms:\n', 1)[1].split('* Constants/Inductives', 1)[0].split())
    inherited = set((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    if not set(context) <= inherited:
        raise ValueError('diagnostic adds a non-inherited library axiom')
    s.kernel.kernel(text, context)
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(run_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel=row, inherited_library_axiom_subset=context, recursive_kernel_check=True,
        all_three_theorems_closed=True, c_execution_counterexample=False, target_correction=False), indent=2) + '\n',
        HERE / 'identity-kernel.log': text})
    print('Frozen identity diagnostic recursively kernel-checked; no C result mismatch claimed', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel'}:
        raise SystemExit('usage: verify.py compile|kernel')
    {'compile': compile, 'kernel': kernel}[sys.argv[1]]()
