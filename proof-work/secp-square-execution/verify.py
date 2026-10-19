"""Audit actual optimized square execution; do not count it as jet equivalence."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('square_ordinary_basis', HERE.parent / 'secp-beta-integration/verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.reporter.g
EXT = Path('/private/tmp/jet-square-execution.eFdtoj')
ROOT = 'SquareRun.Run'
EXTRA = ['-Q', str(EXT), 'SquareRun']


def source_object(path):
    return dict(source_sha256=s.sha(path.read_bytes()), object_sha256=s.sha(path.with_suffix('.vo').read_bytes()))


def source_review():
    paths = ['Haskell/Core/Simplicity/CoreJets.hs', 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs']
    for name in paths:
        if (REPO / name).read_bytes() != subprocess.check_output(['git', 'show', '91d89bac:' + name], cwd=REPO):
            raise ValueError('square specification authority changed')
    for name, fragment in [(paths[0], 'FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE'),
            (paths[0], 'specificationSecp256k1 FeSquare = Secp256k1.fe_square'),
            (paths[1], 'fe_square = iden &&& iden >>> fe_multiply')]:
        if (REPO / name).read_text().count(fragment) != 1:
            raise ValueError('square catalog/program wiring differs')
    code = s.safe_source((HERE / 'Run.v.source').read_text(), ROOT)
    compact = lambda text: re.sub(r'\s+', '', text)
    wanted = 'Definition literal_fe_square {term : Alg.Core.Algebra} : term (Word 8) (Word 8) := iden &&& iden >>> @literal_fe_multiply term.'
    if compact(code).count(compact(wanted)) != 1:
        raise ValueError('literal square program bridge differs')
    return {name: s.sha((REPO / name).read_bytes()) for name in paths}


def identity():
    v.check()
    work, prep, build = v.built()
    source = EXT / 'Run.v'
    if source.is_symlink() or source.read_bytes() != (HERE / 'Run.v.source').read_bytes():
        raise ValueError('square source/archive differs')
    s.safe_source(source.read_text(), ROOT)
    known = {name.removeprefix('Coq/'): dict(source_sha256=row['sha256'], object_sha256=build['source_objects'][name])
        for name, row in prep['sources'].items()}
    return work, source, known, source_review()


def profiles(results, definitions, deps):
    if len(results) != 12 or len(definitions) != 6 or set(results) != set(deps):
        raise ValueError('square foundation report inventory differs')
    if any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('square foundation gained unreviewed assumptions')
    if set(deps[ROOT + '.eval_original_square_owned_inplace']) != s.SIX:
        raise ValueError('actual square C-call inherited profile differs')
    for name in ['square_completes', 'square_run_eq', 'square_return', 'square_regions_count',
            'square_out_shape', 'square_out_defined', 'square_limbs_count', 'literal_square_step']:
        if deps[ROOT + '.' + name]:
            raise ValueError('closed square execution/shape check gained assumptions')


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('square audit already launched; poll original process')
    work, source, known, review = identity()
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        source_sha256=s.sha(source.read_bytes()), driver_sha256=s.sha(Path(__file__).read_bytes())), indent=2) + '\n'})
    commands = {'square-fresh-compile': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(source)], 'square-fresh-compile', 90)}
    results, definitions, deps = g.reports(work, [(ROOT, source)], 'square-audit', commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {name.replace('.', '/') + '.v' for name in libraries if name.startswith(('C.', 'Simplicity.', 'Util.'))}
    unknown = {name for name in libraries if not name.startswith(('C.', 'Simplicity.', 'Util.', 'SquareRun.',
        'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or not local <= set(known):
        raise ValueError('square loaded closure differs from checked ordinary basis')
    identity()
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main proof sources/staging changed during square audit')
    r = dict(candidate=str(EXT), basis=str(work), results=results, definitions=definitions,
        dependencies={name: sorted(ds) for name, ds in deps.items()}, commands=commands,
        source_objects=source_object(source), loaded_local_source_objects={name: known[name] for name in sorted(local)},
        main_inputs=before, staged_patch_sha256=index, source_review_inputs=review,
        parent_checked_sha256=s.sha((v.HERE / 'CHECKED.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False,
        actual_original_square_wrapper_execution=True, numeric_C_square_bridge_proved=False,
        whole_square_jet_proved=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
        HERE / 'square-audit-assumptions.log': (work / 'square-audit-assumptions.log').read_text(),
        HERE / 'square-audit-contracts.log': (work / 'square-audit-contracts.log').read_text(),
        HERE / 'loaded-libraries.log': query.stdout})
    print('Actual square execution/representation reports passed; C numeric bridge and public jet remain unproved', flush=True)


def bound():
    work, source, known, review = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['source_objects'] != source_object(source) or r['source_review_inputs'] != review or
            r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or
            r['parent_checked_sha256'] != s.sha((v.HERE / 'CHECKED.json').read_bytes()) or
            any(known[name] != row for name, row in r['loaded_local_source_objects'].items())):
        raise ValueError('square exact proof inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('square compiler/report log differs: ' + stem)
    return work, r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def kernel():
    work, r = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('square kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=kernel_command(), complete=False,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(), 'square-audit-kernel', 900)
    log = (work / 'square-audit-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(kernel=row,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=True,
        whole_square_jet_proved=False, coverage_added=0), indent=2) + '\n', HERE / 'square-audit-kernel.log': log})
    print('Actual optimized square C-call foundation recursively kernel-checked; no square-jet equivalence claim', flush=True)


def check():
    work, report = bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'square-audit-kernel.log').read_bytes()) or
            (HERE / 'square-audit-kernel.log').read_bytes() != (work / 'square-audit-kernel.log').read_bytes()):
        raise ValueError('square completed kernel evidence differs')
    s.kernel.kernel((HERE / 'square-audit-kernel.log').read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact square execution-foundation sources/objects/reports/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
