"""Audit actual separate-output C square execution; not a complete rescale jet."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('separate_square_preparation', HERE / 'prepare.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
s, g = a.s, a.p.reporter.g
NAMES = ['Layout', 'Run', 'Numeric', 'Caller']
ROOTS = ['SquareSeparate.Numeric', 'SquareSeparate.Caller']
PREFIX = 'square-separate'
FOUR = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
EXPECTED_CALLER = r'''rho m bout bin :
  square_input_bounds rho -> Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin 0 (words5 rho) -> Mem.range_perm m bin 0 40 Cur Freeable -> bout <> bin ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bout 0 (words5 (square_words rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
    fe_at mf bin 0 (words5 rho) /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
    radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\
    lframe (fun b _ => b <> bout /\ b <> bin) m mf.'''


def review(texts):
    compact = lambda x: re.sub(r'\s+', '', s.scanner.code_only(x))
    source = s.scanner.code_only(texts['Caller'])
    statements = re.findall(r'\bTheorem\s+eval_square_separate_from_storage\b(.*?)\bProof\s*\.', source, re.S)
    if len(statements) != 1 or compact(statements[0]) != compact(EXPECTED_CALLER):
        raise ValueError('separate square storage contract changed')
    fragments = {
        'Layout': ['xfun (genv_cenv secp_ge) [] field_table 400 f_secp256k1_fe_sqr [XP 0 0;XP 1 0]',
            'mkreg (map (fun ofs => mkcell ofs Mint64 None) [0;8;16;24;32]) true (Some 40)'],
        'Run': ['Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr) '
            '[Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vptr (blk layout 1) (Ptrofs.repr (bas layout 1))] E0 mf Vundef'],
        'Numeric': ['@literal_fe_square Alg.CoreFunSem x',
            'radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime'],
    }
    for name, parts in fragments.items():
        for fragment in parts:
            if compact(texts[name]).count(compact(fragment)) != 1:
                raise ValueError('original separate square implementation/value target changed: ' + name)


def source_tests(texts):
    cases = [('Layout', '[XP 0 0;XP 1 0]', '[XP 0 0;XP 0 0]'),
        ('Layout', 'mkcell ofs Mint64 None', 'mkcell ofs Mint64 (Some (XLv 0))'),
        ('Run', 'Internal f_secp256k1_fe_sqr', 'Internal f_secp256k1_fe_mul'),
        ('Numeric', '@literal_fe_square Alg.CoreFunSem x', '@literal_fe_multiply Alg.CoreFunSem (x,x)'),
        ('Caller', 'square_input_bounds rho -> Mem.range_perm', 'False -> square_input_bounds rho -> Mem.range_perm'),
        ('Caller', r'fe_at mf bin 0 (words5 rho) /\ ', r'True /\ '),
        ('Caller', r'b <> bout /\ b <> bin', 'False')]
    for name, old, new in cases:
        if old not in texts[name]:
            raise ValueError('missing separate square mutation fixture: ' + old)
        altered = dict(texts); altered[name] = texts[name].replace(old, new, 1)
        try:
            review(altered)
        except ValueError:
            continue
        raise ValueError('separate square mutation escaped: ' + old)
    return len(cases)


def identity():
    work, ext, prep = a.identity()
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected separate square module inventory')
    texts = {}
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('separate square source/archive differs: ' + n)
        texts[n] = p.read_text()
        s.safe_source(texts[n], 'SquareSeparate.' + n)
    review(texts)
    return work, ext, prep, source_tests(texts)


def objects(ext):
    return {n: dict(source_sha256=s.sha((ext / (n + '.v')).read_bytes()),
        object_sha256=s.sha((ext / (n + '.vo')).read_bytes())) for n in NAMES}


def profiles(results, definitions, deps):
    six = {'SquareSeparate.Run.eval_original_square_separate',
        'SquareSeparate.Numeric.eval_original_square_separate_numeric',
        'SquareSeparate.Numeric.eval_original_square_separate_literal',
        'SquareSeparate.Caller.eval_square_separate_from_storage'}
    four = {'SquareSeparate.Numeric.separate_result_loads',
        'SquareSeparate.Caller.field_words_region', 'SquareSeparate.Caller.separate_square_initial_rep',
        'SquareSeparate.Caller.separate_input_field', 'SquareSeparate.Caller.separate_output_field'}
    if len(results) != 20 or len(definitions) != 7 or set(deps) != set(results):
        raise ValueError('separate square declaration inventory differs')
    for n, ds in deps.items():
        wanted = s.SIX if n in six else FOUR if n in four else set()
        if set(ds) != wanted:
            raise ValueError('separate square exact dependency profile differs: ' + n + ' ' + str(ds))


def kernel_command(ext):
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o -Q ' + str(ext) + ' SquareSeparate ' + ' '.join(ROOTS)]


def compile():
    work, ext, prep, mutations = identity()
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('separate square audit already launched; poll original process')
    before, index = s.input_map(), s.index_hash()
    tools = {str(p.relative_to(REPO)): s.sha(p.read_bytes()) for p in [Path(__file__), HERE / 'prepare.py',
        HERE.parent / 'elements-tap-getters/check.py', HERE.parent / 'elements-count/support.py',
        REPO / 'Coq/scan-jet-proofs.py']}
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(complete=False, tools_sha256=tools,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()), source_objects=objects(ext)), indent=2) + '\n'})
    extra = ['-Q', str(ext), 'SquareSeparate']
    commands = {}
    for n in NAMES:
        stem = PREFIX + '-compile-' + n.lower()
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(ext / (n + '.v'))], stem, 90)
    results, definitions, deps = g.reports(work, [('SquareSeparate.' + n, ext / (n + '.v')) for n in NAMES], PREFIX, commands, extra)
    profiles(results, definitions, deps)
    authority = a.p.square_source.source_review()
    for name, digest in authority.items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('separate square canonical source differs: ' + name)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ' '.join(ROOTS) + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    libraries = set(re.findall(r'^\s+([A-Za-z_][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {'Coq/' + n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    private = {n for n in libraries if n.startswith('SquareSeparate.')}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.', 'SquareSeparate.',
        'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or unknown or
            not local <= set(prep['sources']) or private != {'SquareSeparate.' + n for n in NAMES}):
        raise ValueError('separate square loaded unreviewed local/private modules')
    for stem, command, deadline in [
            (PREFIX + '-frozen-targets', [sys.executable, '-B', str(REPO / 'Coq/check-jet-source-target.py')], 60),
            (PREFIX + '-ast', ['bash', 'C/check-secp-jets-generation.sh'], 180)]:
        commands[stem] = s.run(work, command, stem, deadline)
    identity()
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('separate square main/staged inputs changed during audit')
    record = dict(candidate=str(ext), basis=str(work), results=results, definitions=definitions,
        dependencies={n: sorted(ds) for n, ds in deps.items()}, commands=commands, source_objects=objects(ext),
        source_mutations_rejected=mutations, canonical_source_authority=authority,
        loaded_local_source_objects={n: dict(source_sha256=prep['sources'][n], object_sha256=prep['source_objects'][n]) for n in sorted(local)},
        main_inputs=before, staged_patch_sha256=index, tools_sha256=tools,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        recursive_kernel_check=False, actual_separate_square_C_call_proved=True,
        whole_gej_rescale_jet_proved=False, accepted=False, coverage_added=0)
    changes = {HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout}
    for stem in commands:
        changes[HERE / (stem + '.log')] = (work / (stem + '.log')).read_text()
    s.changed(changes)
    print('Actual separate-output C square: execution, numeric/literal bridges and concrete storage contract audited', flush=True)


def bound():
    work, ext, prep, mutations = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['source_objects'] != objects(ext) or r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['preparation_sha256'] != s.sha((HERE / 'PREPARATION.json').read_bytes()) or
            r['source_mutations_rejected'] != mutations or r['canonical_source_authority'] != a.p.square_source.source_review()):
        raise ValueError('separate square exact audited inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for n, digest in r['tools_sha256'].items():
        if s.sha((REPO / n).read_bytes()) != digest:
            raise ValueError('separate square audit tool changed: ' + n)
    for stem, row in r['commands'].items():
        if (row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()) or
                (HERE / (stem + '.log')).read_bytes() != (work / (stem + '.log')).read_bytes()):
            raise ValueError('separate square command/log differs: ' + stem)
    return work, ext, r


def kernel():
    work, ext, r = bound()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('separate square kernel already launched; poll original process')
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(complete=False, command=kernel_command(ext),
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(work, kernel_command(ext), PREFIX + '-kernel', 1200)
    log = (work / (PREFIX + '-kernel.log')).read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(recursive_kernel_check=True, kernel=row,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), whole_gej_rescale_jet_proved=False,
        accepted=False, coverage_added=0), indent=2) + '\n', HERE / (PREFIX + '-kernel.log'): log})
    print('Actual separate-output C square and its concrete caller bridge recursively kernel-checked', flush=True)


def check():
    work, ext, r = bound()
    k = json.loads((HERE / 'CHECKED.json').read_text())
    if (not k['recursive_kernel_check'] or k['kernel']['exit_code'] or k['kernel']['command'] != kernel_command(ext) or
            k['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            k['kernel']['log_sha256'] != s.sha((work / (PREFIX + '-kernel.log')).read_bytes()) or
            (HERE / (PREFIX + '-kernel.log')).read_bytes() != (work / (PREFIX + '-kernel.log')).read_bytes()):
        raise ValueError('separate square completed kernel evidence differs')
    print('Exact separate-output C square sources, objects, reports and kernel receipts match')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
