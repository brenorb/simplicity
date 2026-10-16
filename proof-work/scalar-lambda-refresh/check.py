"""Revalidate the existing initialized lambda proof over accepted418.

No old audit is restarted or certified from its success-looking log. Sources
are namespace-only transports of the existing checked archives; two modules
already present in418 are reused byte-for-byte, not overwritten.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


s = load('lambda_refresh_support', HERE.parent / 'elements-count/support.py')
OLD = HERE.parent / 'scalar-lambda-integration'
OLD_ASSEMBLY = json.loads((OLD / 'ASSEMBLY.json').read_text())
OLD_TREE = Path(OLD_ASSEMBLY['candidate'])
BASE_RECEIPT = HERE.parent / 'elements-txid-admission/MAIN-ACCEPTANCE.json'
BASE_TREE = Path(json.loads((HERE.parent / 'elements-txid-admission/ASSEMBLY.json').read_text())['candidate'])
MODULES = ['C.' + row['name'] for row in OLD_ASSEMBLY['modules']]
REUSED = ['C/jet_clight_forward.v', 'C/jet_frame_constructible.v']
NEW_SOURCES = [m.replace('.', '/') + '.v' for m in MODULES if m.replace('.', '/') + '.v' not in REUSED]
EIGHT = s.SIX | {'Events.external_functions_properties', 'Events.inline_assembly_properties'}
ROOTS = ['C.jet_secp_scalar_lambda_local', 'C.jet_secp_scalar_lambda_fresh']
PREFIXES = ('BorrowC.', 'BorrowFC.', 'LambdaC.', 'LamSpecC.', 'ReadonlyC.', 'LamCallC.', 'LamInitC.', 'LamFrameC.')
KERNEL_COMMAND = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(ROOTS)]


def transport(text):
    for prefix in PREFIXES:
        text = text.replace(prefix, 'C.')
    return text


def sources():
    result = {}
    for row in OLD_ASSEMBLY['modules']:
        p = Path(row['archive'])
        raw = p.read_bytes()
        normal = transport(raw.decode()).encode()
        n = 'C/' + row['name'] + '.v'
        if (s.sha(raw) != row['original_sha256'] or s.sha(normal) != row['candidate_sha256'] or
            s.sha(normal) != OLD_ASSEMBLY['added_file_hashes'][n] or
            (OLD_TREE / 'Coq' / n).read_bytes() != normal):
            raise ValueError('archived/old normal proof source changed: ' + n)
        code = s.safe_source(normal.decode(), n)
        if (re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M) != row['results'] or
            re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', code, re.M) != row['definitions']):
            raise ValueError('declaration inventory changed')
        result[n] = normal.decode()
    return result


def baseline():
    r = json.loads(BASE_RECEIPT.read_text())
    if (r['actual_main_acceptance'] is not True or r['exit_code'] != 0 or
        r['audit_input_sha256'] != s.inputs.fingerprint(BASE_TREE / 'Coq', BASE_TREE)):
        raise ValueError('actual accepted418 baseline differs')
    for name, h in OLD_ASSEMBLY['inherited_dependency_hashes'].items():
        if s.sha((BASE_TREE / 'Coq/C' / (name + '.v')).read_bytes()) != h:
            raise ValueError('old proof dependency differs from418: ' + name)
    for n in REUSED:
        if (BASE_TREE / 'Coq' / n).read_text() != sources()[n]:
            raise ValueError('reused shared proof differs')
    return r


def tree(work):
    r = baseline()
    if work == BASE_TREE or work == OLD_TREE or work == REPO or REPO in work.parents:
        raise ValueError('use a distinct external proof tree')
    paths = load('lambda_refresh_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    inherited = paths(BASE_TREE / 'Coq')
    if paths(work / 'Coq') != inherited | set(NEW_SOURCES):
        raise ValueError('unexpected source/metadata inventory')
    for n in inherited:
        if (work / 'Coq' / n).read_bytes() != (BASE_TREE / 'Coq' / n).read_bytes():
            raise ValueError('inherited source changed: ' + n)
    for n, source in sources().items():
        if (work / 'Coq' / n).read_text() != source:
            raise ValueError('refreshed source is not exact archive transport')
    return r


def assemble(work):
    if (HERE / 'ASSEMBLY.json').exists():
        raise ValueError('already assembled; use the recorded private tree')
    r = baseline()
    before, index = s.input_map(), s.index_hash()
    paths = load('lambda_refresh_assembly_inventory', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    if work == BASE_TREE or work == OLD_TREE or work.parent != Path('/private/tmp'):
        raise ValueError('use a private distinct seed')
    if paths(work / 'Coq') != paths(BASE_TREE / 'Coq'):
        raise ValueError('seed is not exact baseline inventory')
    for n in paths(BASE_TREE / 'Coq'):
        if (work / 'Coq' / n).read_bytes() != (BASE_TREE / 'Coq' / n).read_bytes():
            raise ValueError('seed differs from accepted418')
    proposed = sources()
    if (len(MODULES), len(NEW_SOURCES), len(REUSED)) != (28, 26, 2):
        raise ValueError('wrong fresh/reused source scope')
    s.changed({work / 'Coq' / n: proposed[n] for n in NEW_SOURCES})
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main/index changed during assembly')
    record = dict(candidate=str(work), baseline=str(BASE_TREE), baseline_input_sha256=r['audit_input_sha256'],
        baseline_main_acceptance_sha256=s.sha(BASE_RECEIPT.read_bytes()),
        old_assembly_sha256=s.sha((OLD / 'ASSEMBLY.json').read_bytes()), modules=MODULES,
        new_sources=NEW_SOURCES, reused_sources=REUSED, main_inputs=before, staged_patch_sha256=index,
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())}, normal_registration=False,
        coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'ASSEMBLY.json': json.dumps(record, indent=2) + '\n'})
    print('26 source additions assembled over accepted418; two shared sources reused exactly; registries unchanged', flush=True)


def expected_dependencies():
    old = load('lambda_refresh_old_report', OLD / 'review-normal.py')
    return old.dependencies(OLD_ASSEMBLY, OLD_TREE / 'Coq')


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('checker already launched; inspect its existing handle')
    tree(work)
    assembly = json.loads((HERE / 'ASSEMBLY.json').read_text())
    before, index = s.input_map(), s.index_hash()
    if assembly['candidate'] != str(work) or assembly['main_inputs'] != before or assembly['staged_patch_sha256'] != index:
        raise ValueError('assembly source/main/index differs')
    fp = s.inputs.fingerprint(work / 'Coq', work)
    commands = {}
    for m in MODULES:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m, 300)
        print('compiled ' + m, flush=True)
    results = ['C.' + row['name'] + '.' + n for row in OLD_ASSEMBLY['modules'] for n in row['results']]
    definitions = ['C.' + row['name'] + '.' + n for row in OLD_ASSEMBLY['modules'] for n in row['definitions']]
    if (len(results), len(definitions)) != (116, 32):
        raise ValueError('wrong theorem/definition inventory')
    header = ['Require ' + ' '.join(MODULES) + '.']
    assumptions = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    for kind, names in [('TYPE', results), ('DEF', definitions)]:
        for n in names:
            contracts += ['Goal True. idtac "LAMBDA_REFRESH_' + kind + ' ' + n + '". exact I. Qed.',
                          ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    for stem, lines in [('lambda-refresh-assumptions', assumptions), ('lambda-refresh-contracts', contracts)]:
        p = work / (stem.replace('-', '_') + '.v')
        s.changed({p: '\n'.join(lines) + '\n'})
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(p)], stem, 300)
    deps = s.reports.assumptions((work / 'lambda-refresh-assumptions.log').read_text())
    report = (work / 'lambda-refresh-contracts.log').read_text()
    if (deps != expected_dependencies() or set(deps) != set(results) or any(not ds <= EIGHT for ds in deps.values()) or
        any(deps[m + '.' + n] != EIGHT for m, n in [(ROOTS[0], 'scalar_lambda_initialized_local_spec'),
            (ROOTS[1], 'scalar_lambda_runs_from_actual_init')]) or
        '...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^LAMBDA_REFRESH_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('new assumptions or incomplete/untruncated reports')
    r = dict(candidate=str(work), assembly_sha256=s.sha((HERE / 'ASSEMBLY.json').read_bytes()),
        candidate_input_sha256=fp, modules=MODULES, fresh_modules=MODULES, results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, closed_results=[n for n in results if not deps[n]],
        commands=commands, tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        source_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.v')).read_bytes()) for m in MODULES},
        object_sha256={m: s.sha((work / 'Coq' / (m.replace('.', '/') + '.vo')).read_bytes()) for m in MODULES},
        main_inputs=before, staged_patch_sha256=index, recursive_kernel_check=False,
        canonical_source_guard=False, normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
               **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('116 results/32 definitions freshly compiled and reported; checking source and recursive kernel', flush=True)
    checks = [
        ('source', [sys.executable, '-B', str(OLD / 'check-lambda-public.py'), '--repo', str(REPO), '--coq', str(work / 'Coq')], 300),
        ('source-negative', [sys.executable, '-B', str(OLD / 'test-lambda-public.py'), str(REPO), str(work / 'Coq')], 600),
        ('kernel', KERNEL_COMMAND, 1800)]
    for n, command, timeout in checks:
        commands[n] = s.run(work, command, n, timeout)
        print('passed ' + n, flush=True)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(work / 'Coq', work) != fp:
        raise ValueError('main/index/private source drift')
    r.update(commands=commands, recursive_kernel_check=True, canonical_source_guard=True)
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['source', 'source-negative', 'kernel']}})
    print('Initialized lambda chain refreshed over accepted418; no normal registration or acceptance claim', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['assemble', 'check']:
        raise ValueError('usage: check.py assemble|check PRIVATE_TREE')
    (assemble if sys.argv[1] == 'assemble' else main)(Path(sys.argv[2]).resolve())
