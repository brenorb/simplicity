"""Exact-input audit of the original square helper's numeric/literal bridge.

This does not prove or register the whole public square jet.
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
sp = importlib.util.spec_from_file_location('square_checked_execution', HERE.parent / 'secp-square-execution/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s, g = p.s, p.g
EXT = Path('/private/tmp/jet-square-values.JhhZ8P')
NAMES = ['Algebra', 'Columns', 'Schedule', 'Denote', 'Equality', 'Link', 'Lists', 'Numeric', 'Execution', 'Spec']
EXTRA = p.EXTRA + ['-Q', str(EXT), 'SquareValue']
ROOT = 'SquareValue.Spec'
PREFIX = 'square-values'


def identity():
    p.check()
    work, prep, build = p.v.built()
    if {f.name for f in EXT.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected square extension source inventory')
    for name in NAMES:
        source = EXT / (name + '.v')
        if source.is_symlink() or source.read_bytes() != (HERE / (name + '.v.source')).read_bytes():
            raise ValueError('square numeric source/archive differs: ' + name)
        s.safe_source(source.read_text(), 'SquareValue.' + name)
    known = {name.removeprefix('Coq/'): dict(source_sha256=row['sha256'], object_sha256=build['source_objects'][name])
        for name, row in prep['sources'].items()}
    return work, known


def objects():
    return {name: dict(source_sha256=s.sha((EXT / (name + '.v')).read_bytes()),
        object_sha256=s.sha((EXT / (name + '.vo')).read_bytes())) for name in NAMES}


def profiles(results, definitions, deps):
    if len(results) != 64 or len(definitions) != 47 or set(results) != set(deps):
        raise ValueError('square numeric declaration/report inventory differs')
    if any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('square numeric result gained unreviewed assumptions')
    for name in ['SquareValue.Execution.eval_original_square_owned_numeric',
            'SquareValue.Spec.eval_original_square_literal_from_reader']:
        if set(deps[name]) != s.SIX:
            raise ValueError('actual square execution profile differs: ' + name)
    for name, ds in deps.items():
        if name.startswith(('SquareValue.Algebra.', 'SquareValue.Columns.', 'SquareValue.Equality.',
                'SquareValue.Link.', 'SquareValue.Lists.')) and ds:
            raise ValueError('closed square arithmetic/syntax proof gained assumptions: ' + name)


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('numeric square audit already launched; poll its original process')
    work, known = identity()
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        sources={n: s.sha((EXT / (n + '.v')).read_bytes()) for n in NAMES},
        driver_sha256=s.sha(Path(__file__).read_bytes())), indent=2) + '\n'})
    commands = {}
    for name in NAMES:
        stem = PREFIX + '-compile-' + name.lower()
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA,
            str(EXT / (name + '.v'))], stem, 180 if name == 'Link' else 90)
        print('Fresh compiled SquareValue.' + name, flush=True)
    results, definitions, deps = g.reports(work,
        [('SquareValue.' + n, EXT / (n + '.v')) for n in NAMES], PREFIX, commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.', 'SquareRun.',
        'SquareValue.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    private = {n for n in libraries if n.startswith(('SquareRun.', 'SquareValue.'))}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or
            not local <= set(known) or private != {p.ROOT, *('SquareValue.' + n for n in NAMES)}):
        raise ValueError('numeric square loaded closure differs from the checked basis')
    identity()
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main inputs or staging changed during numeric square audit')
    r = dict(candidate=str(EXT), basis=str(work), modules=NAMES, root=ROOT, results=results,
        definitions=definitions, dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        source_objects=objects(), loaded_local_source_objects={n: known[n] for n in sorted(local)},
        main_inputs=before, staged_patch_sha256=index,
        parent_checked_sha256=s.sha((p.HERE / 'CHECKED.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False,
        numeric_C_square_bridge_proved=True, literal_from_reader_representation_proved=True,
        public_reader_writer_lifecycle_proved=False, whole_square_jet_proved=False, coverage_added=0)
    changes = {HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in [PREFIX + '-assumptions', PREFIX + '-contracts']:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('64 square numeric/literal helper results and 47 definitions audited; public lifecycle remains', flush=True)


def bound():
    work, known = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['source_objects'] != objects() or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['parent_checked_sha256'] != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or
            any(known[n] != row for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('numeric square exact proof inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('numeric square compiler/report log differs: ' + stem)
    return work, r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def kernel():
    work, r = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('numeric square kernel audit already launched; poll its original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=kernel_command(), complete=False,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(), PREFIX + '-kernel', 1200)
    log = (work / (PREFIX + '-kernel.log')).read_text()
    expected = sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    s.kernel.kernel(log, expected)
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(kernel=row, recursive_kernel_check=True,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), numeric_C_square_bridge_proved=True,
        whole_square_jet_proved=False, coverage_added=0), indent=2) + '\n', HERE / (PREFIX + '-kernel.log'): log})
    print('Original C square numeric/literal helper boundary recursively kernel-checked', flush=True)


def check():
    work, _ = bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / (PREFIX + '-kernel.log')).read_bytes()) or
            (HERE / (PREFIX + '-kernel.log')).read_bytes() != (work / (PREFIX + '-kernel.log')).read_bytes()):
        raise ValueError('numeric square completed kernel evidence differs')
    s.kernel.kernel((HERE / (PREFIX + '-kernel.log')).read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact numeric square sources/objects/reports/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
