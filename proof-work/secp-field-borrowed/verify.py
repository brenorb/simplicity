"""Exact source-built audit of the borrowed field multiplier helper chain.

The sealed bases are checked by their actual source/object/kernel inputs,
not by pretending their old entire-checkout preservation sentinels still match.
This packet does not register or claim the complete beta jet.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('borrowed_mul_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('borrowed_mul_reporter', HERE.parent / 'elements-tap-getters/check.py')
BASE = HERE.parent / 'secp-field-integration'
WORK = Path('/private/tmp/jet-field-integration-en95autk')
EXT = Path('/private/tmp/jet-field-borrowed.iX2Dvt')
BORROW = WORK / 'borrowed-probe'
NAMES = ['Transport', 'Runs', 'Body', 'Call']
ROOT = 'FieldBorrowed.Call'
EXTRA = ['-Q', str(BORROW), 'FieldBorrow', '-Q', str(EXT), 'FieldBorrowed']


def source_object(p):
    return dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))


def basis():
    for name in ['field', 'borrowed']:
        result = subprocess.run([sys.executable, '-B', str(HERE.parent / 'check-sealed-jet-bases.py'), name],
            cwd=REPO, env=s.ENV, text=True, capture_output=True, timeout=60)
        if result.returncode:
            raise ValueError('sealed basis check failed: ' + result.stdout + result.stderr)
    prep, built = [json.loads((BASE / n).read_text()) for n in ['PREPARATION.json', 'BUILT.json']]
    if prep['candidate'] != str(WORK):
        raise ValueError('different field basis')
    local = {name.removeprefix('Coq/'): dict(source_sha256=row['sha256'],
        object_sha256=built['source_objects'][name]) for name, row in prep['sources'].items()}
    parent = json.loads((HERE.parent / 'secp-borrowed-region/CHECKED.json').read_text())
    if source_object(BORROW / 'Borrow.v') != {n: parent[n] for n in ['source_sha256', 'object_sha256']}:
        raise ValueError('different borrowed metadata basis')
    return local


def profile(results, definitions, deps):
    six = {'FieldBorrowed.Body.borrowed_stage', 'FieldBorrowed.Body.borrowed_original_body',
        'FieldBorrowed.Call.borrowed_body_for_call', 'FieldBorrowed.Call.eval_original_field_mul_inner_borrowed',
        'FieldBorrowed.Call.borrowed_wrapper_body', 'FieldBorrowed.Call.eval_original_field_mul_wrapper_borrowed',
        'FieldBorrowed.Call.eval_original_field_mul_wrapper_borrowed_product'}
    if (len(results) != 29 or len(definitions) != 4 or not six <= set(results) or
            set(deps) != set(results) or any(not set(ds) <= s.SIX for ds in deps.values()) or
            any(set(deps[n]) != s.SIX for n in six)):
        raise ValueError('borrowed helper inventory or inherited assumption profile differs')


def identity():
    known = basis()
    own = []
    for name in NAMES:
        p = EXT / (name + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (name + '.v.source')).read_bytes():
            raise ValueError('borrowed archive/source mismatch: ' + name)
        s.safe_source(p.read_text(), 'FieldBorrowed.' + name)
        own.append(('FieldBorrowed.' + name, p))
    return known, own


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('borrowed compilation already launched; poll original handle')
    known, own = identity()
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        driver_sha256=s.sha(Path(__file__).read_bytes()), source_inventory={m: s.sha(p.read_bytes()) for m, p in own}), indent=2) + '\n'})
    commands = {}
    for module, p in own:
        commands[module] = s.run(WORK, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(p)],
            'borrowed-fresh-' + p.stem.lower(), 60)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = g.reports(WORK, own, 'borrowed-multiply', commands, EXTRA)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=WORK / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('borrowed actual loaded closure unavailable')
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    ext = {n for n in libraries if n.startswith(('FieldBorrow.', 'FieldBorrowed.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.',
        'FieldBorrow.', 'FieldBorrowed.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if unknown or not local <= set(known) or ext != {'FieldBorrow.Borrow'} | {m for m, _ in own}:
        raise ValueError('unexpected loaded dependency: ' + str(unknown | (local - set(known))))
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('checkout source inputs/staging changed during borrowed audit')
    identity()
    receipt = dict(candidate=str(EXT), basis=str(WORK), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        loaded_local_source_objects={n: known[n] for n in sorted(local)},
        extension_sources_objects={m: source_object(p) for m, p in own},
        inherited_borrowed_source_object=source_object(BORROW / 'Borrow.v'),
        parent_checked_sha256=s.sha((BASE / 'CHECKED.json').read_bytes()),
        borrowed_basis_checked_sha256=s.sha((HERE.parent / 'secp-borrowed-region/CHECKED.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()),
        reuse_checker_sha256=s.sha((HERE.parent / 'check-sealed-jet-bases.py').read_bytes()),
        main_inputs=before, staged_patch_sha256=index, recursive_kernel_check=False,
        actual_original_inner_and_wrapper_calls=True, borrowed_rhs_requires_no_freeable_permission=True,
        original_product_and_bounds_reused=True, whole_beta_jet_proved=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(receipt, indent=2) + '\n',
        HERE / 'borrowed-multiply-assumptions.log': (WORK / 'borrowed-multiply-assumptions.log').read_text(),
        HERE / 'borrowed-multiply-contracts.log': (WORK / 'borrowed-multiply-contracts.log').read_text(),
        HERE / 'loaded-libraries.log': query.stdout})
    print('Full borrowed-call chain reports passed; beta caller/startup/literal composition remain separate', flush=True)


def bound():
    known, own = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['reuse_checker_sha256'] != s.sha((HERE.parent / 'check-sealed-jet-bases.py').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['parent_checked_sha256'] != s.sha((BASE / 'CHECKED.json').read_bytes()) or
            r['borrowed_basis_checked_sha256'] != s.sha((HERE.parent / 'secp-borrowed-region/CHECKED.json').read_bytes()) or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own} or
            r['inherited_borrowed_source_object'] != source_object(BORROW / 'Borrow.v') or
            any(row != known[n] for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('borrowed compile identity differs')
    profile(r['results'], r['definitions'], r['dependencies'])
    for name, row in r['commands'].items():
        stem = 'borrowed-fresh-' + name.rsplit('.', 1)[1].lower() if name.startswith('FieldBorrowed.') else name
        if row['exit_code'] or row['log_sha256'] != s.sha((WORK / (stem + '.log')).read_bytes()):
            raise ValueError('borrowed compiler/report log differs: ' + name)
    return r


def kernel():
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('borrowed kernel already launched; poll original handle')
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=command,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), complete=False), indent=2) + '\n'})
    row = s.run(WORK, command, 'borrowed-multiply-kernel', 900)
    text = (WORK / 'borrowed-multiply-kernel.log').read_text()
    expected = sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    s.kernel.kernel(text, expected)
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(run_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        kernel=row, recursive_kernel_check=True, whole_beta_jet_proved=False, coverage_added=0), indent=2) + '\n',
        HERE / 'borrowed-multiply-kernel.log': text})
    print('Original borrowed-rhs multiplier calls/product kernel-checked; no whole-beta or new-coverage claim', flush=True)


def check():
    bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    expected = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != expected or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'borrowed-multiply-kernel.log').read_bytes()) or
            (HERE / 'borrowed-multiply-kernel.log').read_bytes() != (WORK / 'borrowed-multiply-kernel.log').read_bytes()):
        raise ValueError('borrowed completed kernel evidence differs')
    s.kernel.kernel((HERE / 'borrowed-multiply-kernel.log').read_text(),
        sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact borrowed multiplication source/object/reports/kernel identities verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
