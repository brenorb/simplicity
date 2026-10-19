"""Exact-input audit of the full original public square jet, not registration."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('square_public_caller_basis', HERE.parent / 'secp-square-caller/verify.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s, g = p.s, p.g
EXT = Path('/private/tmp/jet-square-public.rLmhCR')
NAMES = ['Chain', 'Rest', 'Public', 'Local']
ROOT = 'SquarePublic.Local'
ENDPOINT = ROOT + '.fe_square_local_spec'
EXTRA = p.EXTRA + ['-Q', str(EXT), 'SquarePublic']
PREFIX = 'square-public'


def review_source(texts):
    compact = lambda txt: re.sub(r'\s+', '', s.scanner.code_only(txt))
    checks = {
        'Local': ['Theorem fe_square_local_spec : secp_jet_local_spec f_simplicity_fe_square '
            '(Word 8) (Word 8) (@literal_fe_square Alg.CoreFunSem).'],
        'Rest': ['Definition square_inplace_stmt := match fn_body f_simplicity_fe_square with '
            '| Ssequence _ (Ssequence _ (Ssequence squaring _)) => squaring | _ => Sskip end.',
            'Definition square_rest := match fn_body f_simplicity_fe_square with '
            '| Ssequence _ rest => rest | _ => Sskip end.',
            'Genv.find_symbol secp_ge _secp256k1_fe_sqr = Some (secp_symbol_block _secp256k1_fe_sqr)',
            'Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_fe_sqr) Ptrofs.zero) '
            '= Some (Internal f_secp256k1_fe_sqr).',
            'Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr) '
            '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->'],
        'Public': ['function_entry2 secp_ge f_simplicity_fe_square '
            '[Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m',
            'Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_square)'],
        'Chain': ['Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_sqr) '
            '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn Vundef'],
    }
    for name, fragments in checks.items():
        code = compact(texts[name])
        for fragment in fragments:
            if code.count(compact(fragment)) != 1:
                raise ValueError('square public target/contract/call differs: ' + name)
    if any(re.search(r'\b(?:beta_initialized|memcpy_model|memcmp_model)\b', s.scanner.code_only(t)) for t in texts.values()):
        raise ValueError('unexpected extra readiness/library premise')


def source_tests(texts):
    mutations = [
        ('Local', 'secp_jet_local_spec', 'secp_jet_initialized_local_spec'),
        ('Local', 'f_simplicity_fe_square', 'f_simplicity_fe_normalize'),
        ('Local', '(Word 8) (Word 8)', '(Word 7) (Word 8)'),
        ('Local', '(Word 8) (Word 8)', '(Word 8) (Word 7)'),
        ('Local', '@literal_fe_square', '@canonical_fe_normalize'),
        ('Rest', 'fn_body f_simplicity_fe_square', 'fn_body f_simplicity_fe_multiply_beta'),
        ('Rest', 'Internal f_secp256k1_fe_sqr', 'Internal f_secp256k1_fe_mul'),
        ('Rest', '[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf', '[Vptr ba Ptrofs.zero] E0 mf'),
        ('Public', 'function_entry2 secp_ge f_simplicity_fe_square', 'function_entry2 secp_ge f_simplicity_fe_normalize'),
        ('Public', 'Internal f_simplicity_fe_square', 'Internal f_simplicity_fe_multiply'),
        ('Chain', 'Internal f_secp256k1_fe_sqr', 'Internal f_secp256k1_fe_mul'),
        ('Chain', '[] m ->', '[] m -> beta_initialized m ->'),
    ]
    for name, old, new in mutations:
        if old not in texts[name]:
            raise ValueError('missing square public mutation fixture: ' + old)
        changed = dict(texts)
        changed[name] = texts[name].replace(old, new, 1)
        try:
            review_source(changed)
        except ValueError:
            continue
        raise ValueError('square public source mutation escaped: ' + old)
    return len(mutations)


def identity():
    p.check()
    work, known, _ = p.identity()
    if {f.name for f in EXT.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected public square source inventory')
    texts = {}
    for name in NAMES:
        source = EXT / (name + '.v')
        if source.is_symlink() or source.read_bytes() != (HERE / (name + '.v.source')).read_bytes():
            raise ValueError('public square source/archive differs: ' + name)
        texts[name] = source.read_text()
        s.safe_source(texts[name], 'SquarePublic.' + name)
    review_source(texts)
    return work, known, source_tests(texts)


def objects():
    return {n: dict(source_sha256=s.sha((EXT / (n + '.v')).read_bytes()),
        object_sha256=s.sha((EXT / (n + '.vo')).read_bytes())) for n in NAMES}


def profiles(results, definitions, deps):
    if len(results) != 9 or len(definitions) != 2 or set(results) != set(deps) or any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('public square report inventory/profile differs')
    for name in [ENDPOINT, 'SquarePublic.Public.eval_public_square', 'SquarePublic.Chain.eval_square_read_sqr_write']:
        if set(deps[name]) != s.SIX:
            raise ValueError('public square endpoint inherited profile differs: ' + name)
    for name in ['SquarePublic.Rest.square_rest_eq', 'SquarePublic.Rest.square_helper_symbols', 'SquarePublic.Public.square_public_body']:
        if deps[name]:
            raise ValueError('closed square syntax/linkage check gained assumptions: ' + name)


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('public square audit already launched; poll its original process')
    work, known, mutations = identity()
    before, index = s.input_map(), s.index_hash()
    parent = s.sha((p.HERE / 'CHECKED.json').read_bytes())
    driver = s.sha(Path(__file__).read_bytes())
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        sources={n: s.sha((EXT / (n + '.v')).read_bytes()) for n in NAMES},
        driver_sha256=driver, parent_checked_sha256=parent), indent=2) + '\n'})
    commands = {}
    for n in NAMES:
        stem = PREFIX + '-compile-' + n.lower()
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(EXT / (n + '.v'))], stem, 90)
    commands['square-public-frozen-target'] = s.run(work, [sys.executable, '-B', str(REPO / 'Coq/check-jet-source-target.py')],
        'square-public-frozen-target', 60)
    results, definitions, deps = g.reports(work, [('SquarePublic.' + n, EXT / (n + '.v')) for n in NAMES], PREFIX, commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.', 'SquareRun.',
        'SquareValue.', 'SquareCaller.', 'SquarePublic.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    private = {n for n in libraries if n.startswith(('SquareRun.', 'SquareValue.', 'SquareCaller.', 'SquarePublic.'))}
    expected = {p.ROOT, p.p.p.ROOT, *('SquareValue.' + n for n in p.p.NAMES), *('SquarePublic.' + n for n in NAMES)}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or
            not local <= set(known) or private != expected):
        raise ValueError('public square loaded an unreviewed module')
    identity()
    if before != s.input_map() or index != s.index_hash() or parent != s.sha((p.HERE / 'CHECKED.json').read_bytes()):
        raise ValueError('public square main/staged/parent inputs changed during compilation')
    r = dict(candidate=str(EXT), basis=str(work), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands, source_objects=objects(),
        loaded_local_source_objects={n: known[n] for n in sorted(local)}, source_mutations_rejected=mutations,
        main_inputs=before, staged_patch_sha256=index, parent_checked_sha256=parent, driver_sha256=driver,
        recursive_kernel_check=False, whole_square_jet_proved=True, accepted=False, coverage_added=0)
    changes = {HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in [PREFIX + '-assumptions', PREFIX + '-contracts', 'square-public-frozen-target']:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('Full original square public contract compiled and assumption-audited; 12 source mutations rejected', flush=True)


def bound():
    work, known, mutations = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['source_objects'] != objects() or r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or r['source_mutations_rejected'] != mutations or
            r['parent_checked_sha256'] != s.sha((p.HERE / 'CHECKED.json').read_bytes()) or
            any(known[n] != row for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('public square exact inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('public square compilation/report log differs: ' + stem)
    return work, r


def kernel():
    work, _ = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('public square kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=kernel_command(), complete=False,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(), PREFIX + '-kernel', 1200)
    log = (work / (PREFIX + '-kernel.log')).read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(kernel=row, recursive_kernel_check=True,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), whole_square_jet_proved=True,
        accepted=False, coverage_added=0), indent=2) + '\n', HERE / (PREFIX + '-kernel.log'): log})
    print('Full original public square jet recursively kernel-checked against literal Simplicity', flush=True)


def check():
    work, _ = bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / (PREFIX + '-kernel.log')).read_bytes()) or
            (HERE / (PREFIX + '-kernel.log')).read_bytes() != (work / (PREFIX + '-kernel.log')).read_bytes()):
        raise ValueError('public square completed kernel evidence differs')
    s.kernel.kernel((HERE / (PREFIX + '-kernel.log')).read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact full public square source/object/reports/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
