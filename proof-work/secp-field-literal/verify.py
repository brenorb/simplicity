"""Source-built, source-reviewed, recursively checked public C-to-Simplicity proof."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-public'
PORTS = Path('/private/tmp/jet-multiply-literal-ports.BsO6pV')
sp = importlib.util.spec_from_file_location('literal_checked_public', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['Spec', 'Jet']
ROOT = 'FieldLiteral.Jet'
source_object = v.source_object
loaded_closure = v.loaded_closure


def fresh_closure(known):
    seen, active, order = set(), set(), []
    def visit(m):
        if m in active:
            raise ValueError('cyclic literal dependency: ' + m)
        if m in seen:
            return
        seen.add(m)
        name = m.replace('.', '/') + '.v'
        if name in known:
            return
        active.add(m)
        code = s.safe_source((s.REPO / 'Coq' / name).read_text(), m)
        for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
            for d in block.split():
                if d.startswith(('C.', 'Simplicity.', 'Util.')):
                    visit(d)
        active.remove(m)
        order.append(m)
    for root in ['C.jet_secp_negate_literal_contract', 'C.jet_haskell_word_conversion']:
        visit(root)
    return order


def review_inputs():
    result = {}
    for p in sorted((s.REPO / 'Coq/negate-review').iterdir()):
        if p.is_file() and (p.name.endswith(('.py', '.py.source', '.json'))):
            result[str(p.relative_to(s.REPO))] = s.sha(p.read_bytes())
    for n in ['jet_secp_canonical_negate', 'jet_secp_negate_local', 'jet_literal_division_add',
              'jet_canonical_add_adapter', 'jet_secp_negate_literal_contract', 'jet_haskell_word_conversion']:
        p = PORTS / (n + '.v')
        q = s.REPO / 'Coq/C' / p.name
        if p.read_bytes() != q.read_bytes():
            raise ValueError('review candidate/source mismatch: ' + n)
        result['candidate/' + p.name] = s.sha(p.read_bytes())
    p = PORTS / 'recursive-ports-review.json'
    if p.read_bytes() != (s.REPO / 'Coq/negate-review' / p.name).read_bytes():
        raise ValueError('reviewed recursive reference differs')
    result['candidate/' + p.name] = s.sha(p.read_bytes())
    return result


def identity(work):
    parent = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, parent)
    if (not parent['recursive_kernel_check'] or parent['kernel']['exit_code'] != 0 or
            parent['kernel']['log_sha256'] != s.sha((PARENT / 'public-kernel.log').read_bytes()) or
            parent['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked public function evidence differs')
    dep = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    order = fresh_closure(parent['loaded_local_source_objects'])
    if (len(order) != 25 or list(dep['modules']) != order or dep['candidate'] != str(work) or
            dep['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            dep['main_inputs'] != s.input_map() or dep['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('literal/foundation dependency receipt differs')
    local = dict(parent['loaded_local_source_objects'])
    for m, row in dep['modules'].items():
        name = m.replace('.', '/') + '.v'
        p = work / 'Coq' / name
        if (p.is_symlink() or p.read_bytes() != (s.REPO / 'Coq' / name).read_bytes() or
                row['command'] != ['bash', 'build-jets.sh', '--coqc', '-q', str(p)] or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((work / ('literal-dependency-' + m + '.log')).read_bytes()) or
                {k: row[k] for k in ['source_sha256', 'object_sha256']} != source_object(p)):
            raise ValueError('literal dependency source/object/compilation differs: ' + m)
        s.safe_source(p.read_text(), m)
        local[name] = source_object(p)
    inherited = dict(parent['inherited_extension_sources_objects'])
    inherited.update(parent['extension_sources_objects'])
    ext = work / 'literal'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected literal source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('literal archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldLiteral.' + n)
        own.append(('FieldLiteral.' + n, p))
    return own, parent, inherited, local, extra + ['-Q', str(ext), 'FieldLiteral']


def profile(results, definitions, deps):
    six = {ROOT + '.eval_original_public_field_multiply_literal', ROOT + '.fe_multiply_literal_local_spec'}
    one = {'FieldLiteral.Spec.literal_multiply_numeric', 'FieldLiteral.Spec.input_product_matches_literal'}
    expected = {n: s.SIX if n in six else {'FunctionalExtensionality.functional_extensionality_dep'} for n in results}
    if set(results) != six | one or len(results) != 4 or definitions or deps != expected:
        raise ValueError('literal profile differs: two inherited function-extensionality bridges, two SIX endpoints')


def review_commands():
    commands = {'multiply-source': [sys.executable, '-B', str(HERE / 'check-source.py')]}
    for family in ['negate-wiring', 'recursive-ports', 'literal-ports', 'foundations']:
        for action in ['check', 'test']:
            name = action + '-' + family
            commands[name] = [sys.executable, '-B', str(s.REPO / 'Coq/negate-review' / (name + '.py')),
                '--repo', str(s.REPO), '--candidates', str(PORTS)]
    for action in ['check', 'test']:
        name = action + '-normalize'
        commands[name] = [sys.executable, '-B', str(s.REPO / 'Coq' / (action + '-secp-normalize-specification.py'))]
    commands['original-targets'] = [sys.executable, '-B', str(s.REPO / 'Coq/check-jet-source-target.py')]
    return commands


def bound(work, r):
    own, parent, inherited, local, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['dependency_receipt_sha256'] != s.sha((HERE / 'DEPENDENCIES.json').read_bytes()) or
            r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'check-source.py']} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != local or r['review_inputs'] != review_inputs() or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('literal checked-input identity differs')
    expected = review_commands()
    if set(r['source_review_commands']) != set(expected):
        raise ValueError('missing source correspondence/negative/original-target gate')
    for name, row in r['source_review_commands'].items():
        if (row['command'] != expected[name] or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((work / ('literal-review-' + name + '.log')).read_bytes())):
            raise ValueError('source review command/log differs: ' + name)
    profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    return extra


def negative_checks(r, loaded):
    deps = {n: set(a) for n, a in r['dependencies'].items()}
    bad = {n: set(a) for n, a in deps.items()}
    bad[r['results'][0]].add('Unreviewed.extra_assumption')
    try:
        profile(r['results'], r['definitions'], bad)
    except ValueError:
        pass
    else:
        raise ValueError('extra assumption was accepted')
    local, ext = loaded_closure(loaded)
    if (local != set(r['loaded_local_source_objects']) or
            ext != set(r['inherited_extension_sources_objects']) | set(r['extension_sources_objects'])):
        raise ValueError('literal recorded loaded closure differs')
    if loaded_closure(loaded + '\n  Unreviewed.Unknown\n')[1] == ext:
        raise ValueError('unfamiliar namespace disappeared from loaded inventory')
    return 'Extra assumption rejected; unfamiliar module detected; exact positive loaded closure matched.\n'


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('literal compilation already launched; poll original handle')
    own, parent, inherited, local, extra = identity(work)
    before, index, reviews = s.input_map(), s.index_hash(), review_inputs()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
                            'literal-fresh-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, own, 'literal', commands, extra)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    actual_local, actual_ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            actual_local != set(local) or actual_ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('literal loaded closure lacks exact source-built provenance')
    source_commands = {}
    for name, command in review_commands().items():
        source_commands[name] = s.run(work, command, 'literal-review-' + name, 180)
        print('passed ' + name, flush=True)
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash, dependency_receipt_sha256=s.sha((HERE / 'DEPENDENCIES.json').read_bytes()),
        loaded_local_source_objects=local, inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own}, review_inputs=reviews,
        source_review_commands=source_commands,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'check-source.py']},
        actual_public_function_call_proved=True, full_word256_pair_input_domain=True,
        literal_simplicity_program_composed=True, public_caller_lifecycle_proved=True,
        public_jet_equivalence=True, checked_public_contract=ROOT + '.fe_multiply_literal_local_spec',
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    tests = negative_checks(r, query.stdout)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'negative-checks.log': tests,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['literal-assumptions', 'literal-contracts']},
        **{HERE / ('review-' + name + '.log'): (work / ('literal-review-' + name + '.log')).read_text()
           for name in source_commands}})
    print('Public C-to-literal-Simplicity multiplication equivalence freshly compiled and source-reviewed', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('literal kernel check already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'literal-kernel', 900)
    log = (work / 'literal-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'literal-kernel.log': log})
    print('Complete original public C jet against literal Simplicity specification recursively kernel-checked', flush=True)


def check(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    bound(work, r)
    log = (HERE / 'literal-kernel.log').read_text()
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.encode()) or
            r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((HERE / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes())):
        raise ValueError('literal kernel evidence differs')
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    for name, row in r['source_review_commands'].items():
        if row['log_sha256'] != s.sha((HERE / ('review-' + name + '.log')).read_bytes()):
            raise ValueError('archived source review log differs: ' + name)
    negative_checks(r, (HERE / 'loaded-libraries.log').read_text())
    print('Public C-to-literal-Simplicity jet: exact source/object/parent/driver/review/kernel identities verified', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise ValueError('usage: verify.py compile|kernel|check PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
