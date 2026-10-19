"""Fresh exact-input audit; helper/startup evidence, not public jet acceptance."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('beta_borrowed_audit', HERE.parent / 'secp-field-borrowed/verify.py')
b = importlib.util.module_from_spec(sp)
sp.loader.exec_module(b)
s, g, WORK = b.s, b.g, b.WORK
EXT = Path('/private/tmp/jet-secp-beta-global.VsIuk6')
NAMES = ['Global', 'Inputs', 'Spec', 'Call']
EXTRA = b.EXTRA + ['-Q', str(EXT), 'BetaGlobal']
ROOT = 'BetaGlobal.Call'
DEP = 'C/jet_program_initialization.v'


def source_review():
    # Frozen original Haskell is the port authority. No claim of checking a
    # Haskell compiler or replacing the original specification is made here.
    paths = ['Haskell/Core/Simplicity/LibSecp256k1/Spec.hs',
             'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs',
             'Haskell/Core/Simplicity/CoreJets.hs']
    texts = [(REPO / p).read_text() for p in paths]
    for p, txt in zip(paths, texts):
        if txt != subprocess.check_output(['git', 'show', '91d89bac:' + p], cwd=REPO, text=True):
            raise ValueError('beta port authority changed: ' + p)
    beta = re.findall(r'^beta = (0x[0-9a-f]+)$', texts[0], re.M)
    if beta != ['0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee']:
        raise ValueError('different canonical beta')
    for txt, line in [(texts[1], 'fe_beta = scribe256 LibSecp256k1.beta'),
            (texts[1], ', fe_multiply_beta = (unit >>> fe_beta) &&& iden >>> fe_multiply'),
            (texts[2], 'specificationSecp256k1 FeMultiplyBeta = Secp256k1.fe_multiply_beta')]:
        if txt.count(line) != 1:
            raise ValueError('beta specification wiring changed')
    src = s.safe_source((HERE / 'Global.v.source').read_text(), 'BetaGlobal.Global')
    value = re.findall(r'Definition beta_value\s*:\s*Z\s*:=\s*(\d+)\s*\.', src)
    if value != [str(int(beta[0], 16))]:
        raise ValueError('ported beta value differs from original Haskell')
    src = s.safe_source((HERE / 'Spec.v.source').read_text(), 'BetaGlobal.Spec')
    norm = lambda x: re.sub(r'\s+', '', x)
    for declaration in [
        'Definition beta_word : Ty.tySem (Word 8) := @fromZ (WordToZ 8) beta_value.',
        'Definition literal_fe_beta {term : Alg.Core.Algebra} : term Ty.Unit (Word 8) := Alg.scribe beta_word.',
        'Definition literal_fe_multiply_beta {term : Alg.Core.Algebra} : term (Word 8) (Word 8) := '
            '(unit >>> @literal_fe_beta term) &&& iden >>> @literal_fe_multiply term.']:
        if norm(src).count(norm(declaration)) != 1:
            raise ValueError('beta literal port differs')
    return {p: s.sha((REPO / p).read_bytes()) for p in paths}


def identity():
    b.check()
    known = b.basis()
    dep = WORK / 'Coq' / DEP
    if dep.is_symlink() or dep.read_bytes() != (REPO / 'Coq' / DEP).read_bytes():
        raise ValueError('initialization dependency source differs')
    s.safe_source(dep.read_text(), DEP)
    known[DEP] = b.source_object(dep)
    extknown = {'FieldBorrow.Borrow': b.source_object(b.BORROW / 'Borrow.v')}
    extknown.update({m: b.source_object(p) for m, p in b.identity()[1]})
    own = []
    for name in NAMES:
        p = EXT / (name + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (name + '.v.source')).read_bytes():
            raise ValueError('beta source/archive differs: ' + name)
        s.safe_source(p.read_text(), 'BetaGlobal.' + name)
        own.append(('BetaGlobal.' + name, p))
    return known, extknown, own, source_review()


def profiles(results, definitions, deps):
    if len(results) != 29 or len(definitions) != 16 or set(results) != set(deps):
        raise ValueError('beta report inventory differs')
    if any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('beta proof gained assumptions')
    if set(deps['BetaGlobal.Call.eval_beta_from_reader_storage']) != s.SIX:
        raise ValueError('actual C call inherited profile differs')
    if any(deps['BetaGlobal.Global.' + n] for n in ['beta_symbol', 'beta_var_info',
            'beta_radix_value', 'beta_limb_bounds', 'beta_program_initialization_ok_true']):
        raise ValueError('closed beta constant check gained assumptions')


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('beta compilation already launched; poll original process')
    known, inherited, own, review = identity()
    before, index = s.input_map(), s.index_hash()
    modules = [('C.jet_program_initialization', WORK / 'Coq' / DEP)] + own
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(complete=False, candidate=str(EXT),
        driver_sha256=s.sha(Path(__file__).read_bytes()), sources={m: s.sha(p.read_bytes()) for m, p in modules}), indent=2) + '\n'})
    commands = {}
    for module, p in modules:
        stem = 'beta-fresh-' + module.rsplit('.', 1)[-1].lower()
        commands[stem] = s.run(WORK, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(p)], stem, 60)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = g.reports(WORK, modules, 'beta-audit', commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=WORK / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('beta loaded dependency query failed')
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    exts = {n for n in libraries if n.startswith(('FieldBorrow.', 'FieldBorrowed.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.',
        'FieldBorrow.', 'FieldBorrowed.', 'BetaGlobal.', 'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if unknown or not local <= set(known) or exts != set(inherited):
        raise ValueError('unexpected beta loaded inputs: ' + str(unknown | (local - set(known))))
    identity()
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main sources/staging changed during beta audit')
    r = dict(candidate=str(EXT), basis=str(WORK), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands,
        main_inputs=before, staged_patch_sha256=index, source_review_inputs=review,
        own_sources_objects={m: b.source_object(p) for m, p in own},
        loaded_local_source_objects={n: b.source_object(WORK / 'Coq' / n) for n in sorted(local)},
        inherited_extension_source_objects=inherited,
        borrowed_checked_sha256=s.sha((b.HERE / 'CHECKED.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False,
        actual_beta_initialized_memory_exists=True, unrestricted_Word256=True,
        actual_original_helper_call=True, whole_beta_jet_proved=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
        HERE / 'beta-audit-assumptions.log': (WORK / 'beta-audit-assumptions.log').read_text(),
        HERE / 'beta-audit-contracts.log': (WORK / 'beta-audit-contracts.log').read_text(),
        HERE / 'loaded-libraries.log': query.stdout})
    print('Beta startup/representation/literal-helper reports passed; public caller still unresolved', flush=True)


def bound():
    known, inherited, own, review = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['source_review_inputs'] != review or
            r['borrowed_checked_sha256'] != s.sha((b.HERE / 'CHECKED.json').read_bytes()) or
            r['own_sources_objects'] != {m: b.source_object(p) for m, p in own} or
            r['inherited_extension_source_objects'] != inherited or
            any(known[n] != row for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('beta audited inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((WORK / (stem + '.log')).read_bytes()):
            raise ValueError('beta compilation/report log differs: ' + stem)
    return r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def kernel():
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('beta kernel already launched; poll original process')
    bound()
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=kernel_command(), complete=False,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(WORK, kernel_command(), 'beta-audit-kernel', 900)
    log = (WORK / 'beta-audit-kernel.log').read_text()
    s.kernel.kernel(log, sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(kernel=row,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=True,
        whole_beta_jet_proved=False, coverage_added=0), indent=2) + '\n', HERE / 'beta-audit-kernel.log': log})
    print('Beta initialized-global and actual helper-call chain recursively kernel-checked', flush=True)


def check():
    bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'beta-audit-kernel.log').read_bytes()) or
            (HERE / 'beta-audit-kernel.log').read_bytes() != (WORK / 'beta-audit-kernel.log').read_bytes()):
        raise ValueError('beta completed kernel evidence differs')
    s.kernel.kernel((HERE / 'beta-audit-kernel.log').read_text(),
        sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact beta startup/helper source/object/reports/kernel inputs verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
