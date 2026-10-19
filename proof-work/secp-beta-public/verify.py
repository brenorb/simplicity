"""Exact source-built audit of the complete original initialized beta jet.

No metadata registration or whole-repository acceptance is claimed. Historical
helper receipts are reused only for their exact checked sources and objects.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('public_beta_frame_basis', HERE.parent / 'clight-internal-frame/verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g, WORK = v.s, v.g, v.WORK
EXT = Path('/private/tmp/jet-beta-public.xYJKvR')
EXTRA = v.EXTRA + ['-Q', str(EXT), 'BetaPublic']
NAMES = ['Preserve', 'Graph', 'State', 'Chain', 'Rest', 'Public', 'Local']
DEP = 'C/jet_secp_initialized_contract.v'
ROOT = 'BetaPublic.Local'
ENDPOINT = ROOT + '.fe_multiply_beta_initialized_local_spec'


def contract_source(code):
    code = s.safe_source(code, ROOT)
    header = code.split('Theorem fe_multiply_beta_initialized_local_spec', 1)
    if len(header) != 2:
        raise ValueError('missing beta public theorem')
    actual = header[1].split('Proof.', 1)[0]
    expected = ': secp_jet_initialized_local_spec beta_initialized f_simplicity_fe_multiply_beta '
    expected += '(Word 8) (Word 8) (@literal_fe_multiply_beta Alg.CoreFunSem).'
    if re.sub(r'\s+', '', actual) != re.sub(r'\s+', '', expected):
        raise ValueError('beta public contract was narrowed or retargeted')


def source_review():
    result = v.v.source_review()
    source = (HERE / 'Local.v.source').read_text()
    contract_source(source)
    fixtures = [
        source.replace('(Word 8) (Word 8)', '(Word 7) (Word 8)', 1),
        source.replace('(Word 8) (Word 8)', '(Word 8) (Word 7)', 1),
        source.replace('f_simplicity_fe_multiply_beta (Word', 'f_secp256k1_fe_mul (Word', 1),
        source.replace('sec p', 'sec p').replace('local_spec beta_initialized', 'local_spec (fun _ => True)', 1),
        source.replace('(@literal_fe_multiply_beta Alg.CoreFunSem).', '(@canonical_fe_normalize Alg.CoreFunSem).', 1),
        source.replace('  secp_jet_initialized_local_spec beta_initialized',
            '  False -> secp_jet_initialized_local_spec beta_initialized', 1)]
    for n, fixture in enumerate(fixtures):
        if fixture == source:
            raise ValueError('vacuous beta contract fixture: ' + str(n))
        try:
            contract_source(fixture)
        except ValueError:
            continue
        raise ValueError('beta contract mutation escaped: ' + str(n))
    return dict(authority_inputs=result, exact_initialized_contract=True, rejected_mutations=len(fixtures))


def identity():
    v.check()
    known, inherited, frames = v.identity()
    inherited.update({m: v.v.b.source_object(p) for m, p in frames})
    dep = WORK / 'Coq' / DEP
    if dep.is_symlink() or dep.read_bytes() != (v.v.REPO / 'Coq' / DEP).read_bytes():
        raise ValueError('shared initialized contract source differs')
    s.safe_source(dep.read_text(), DEP)
    known[DEP] = v.v.b.source_object(dep)
    own = []
    for name in NAMES:
        p = EXT / (name + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (name + '.v.source')).read_bytes():
            raise ValueError('beta public source/archive mismatch: ' + name)
        s.safe_source(p.read_text(), 'BetaPublic.' + name)
        own.append(('BetaPublic.' + name, p))
    return known, inherited, own, source_review()


def profiles(results, definitions, deps):
    if len(results) != 28 or len(definitions) != 5 or set(results) != set(deps):
        raise ValueError('beta public theorem/definition inventory differs')
    if any(not set(ds) <= s.SIX for ds in deps.values()):
        raise ValueError('beta public proof acquired new assumptions')
    for name in [ENDPOINT, 'BetaPublic.Public.eval_public_beta', 'BetaPublic.Rest.exec_beta_rest',
            'BetaPublic.Chain.eval_beta_read_mul_write', 'BetaPublic.Preserve.internal_exec_preserved']:
        if set(deps[name]) != s.SIX:
            raise ValueError('beta execution assumption profile differs: ' + name)
    for name in ['beta_internal_table_correct', 'beta_public_allowed', 'beta_reader_allowed', 'beta_writer_allowed']:
        if deps['BetaPublic.Graph.' + name]:
            raise ValueError('closed callgraph check gained assumptions')


def compile():
    if (HERE / 'COMPILE-LAUNCH.json').exists():
        raise ValueError('beta public audit already launched; poll original process')
    known, inherited, own, review = identity()
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'COMPILE-LAUNCH.json': json.dumps(dict(candidate=str(EXT), complete=False,
        driver_sha256=s.sha(Path(__file__).read_bytes()), sources={m: s.sha(p.read_bytes()) for m, p in own}), indent=2) + '\n'})
    commands = {}
    commands['beta-public-contract-dependency'] = s.run(WORK,
        ['bash', 'build-jets.sh', '--coqc', '-q', str(WORK / 'Coq' / DEP)], 'beta-public-contract-dependency', 60)
    for module, p in own:
        stem = 'beta-public-fresh-' + p.stem.lower()
        commands[stem] = s.run(WORK, ['bash', 'build-jets.sh', '--coqc', '-q', *EXTRA, str(p)], stem, 60)
        print('Freshly compiled ' + module, flush=True)
    results, definitions, deps = g.reports(WORK, own, 'beta-public-audit', commands, EXTRA)
    profiles(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *EXTRA],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=WORK / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('beta public loaded-closure query failed')
    libraries = set(re.findall(r'^\s+([A-Z_a-z][\w]*(?:\.[\w]+)+)\s*$', query.stdout, re.M))
    local = {n.replace('.', '/') + '.v' for n in libraries if n.startswith(('C.', 'Simplicity.', 'Util.'))}
    exts = {n for n in libraries if n.startswith(('FieldBorrow.', 'FieldBorrowed.', 'BetaGlobal.', 'InternalFrame.'))}
    unknown = {n for n in libraries if not n.startswith(('C.', 'Simplicity.', 'Util.',
        'FieldBorrow.', 'FieldBorrowed.', 'BetaGlobal.', 'InternalFrame.', 'BetaPublic.',
        'Coq.', 'compcert.', 'Flocq.', 'VST.', 'sha.'))}
    if unknown or not local <= set(known) or exts != set(inherited):
        raise ValueError('beta public closure contains unchecked inputs: ' + str(unknown | (local - set(known))))
    identity()
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main sources/staging changed during beta public audit')
    r = dict(candidate=str(EXT), basis=str(WORK), endpoint=ENDPOINT,
        results=results, definitions=definitions, dependencies={n: sorted(ds) for n, ds in deps.items()},
        commands=commands, main_inputs=before, staged_patch_sha256=index, source_review=review,
        own_sources_objects={m: v.v.b.source_object(p) for m, p in own},
        loaded_local_source_objects={n: v.v.b.source_object(WORK / 'Coq' / n) for n in sorted(local)},
        inherited_extension_source_objects=inherited,
        parent_checked_sha256=s.sha((v.HERE / 'CHECKED.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), recursive_kernel_check=False,
        whole_beta_jet_proved=True, full_initialized_frame_contract=True, unrestricted_Word256=True,
        extra_nonalias_input_condition=False, coverage_added=0, shared_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
        HERE / 'beta-public-audit-assumptions.log': (WORK / 'beta-public-audit-assumptions.log').read_text(),
        HERE / 'beta-public-audit-contracts.log': (WORK / 'beta-public-audit-contracts.log').read_text(),
        HERE / 'loaded-libraries.log': query.stdout})
    print('Complete original beta public-jet types/assumptions/source-contract review passed', flush=True)


def bound():
    known, inherited, own, review = identity()
    r = json.loads((HERE / 'RUN.json').read_text())
    if (r['driver_sha256'] != s.sha(Path(__file__).read_bytes()) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['source_review'] != review or
            r['parent_checked_sha256'] != s.sha((v.HERE / 'CHECKED.json').read_bytes()) or
            r['own_sources_objects'] != {m: v.v.b.source_object(p) for m, p in own} or
            r['inherited_extension_source_objects'] != inherited or
            any(known[n] != row for n, row in r['loaded_local_source_objects'].items())):
        raise ValueError('beta public checked inputs differ')
    profiles(r['results'], r['definitions'], r['dependencies'])
    for stem, row in r['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((WORK / (stem + '.log')).read_bytes()):
            raise ValueError('beta public compiler/report log differs: ' + stem)
    return r


def kernel_command():
    return ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(EXTRA + [ROOT])]


def kernel():
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('beta public kernel already launched; poll original process')
    bound()
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(command=kernel_command(), complete=False,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes())), indent=2) + '\n'})
    row = s.run(WORK, kernel_command(), 'beta-public-audit-kernel', 900)
    log = (WORK / 'beta-public-audit-kernel.log').read_text()
    s.kernel.kernel(log, sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(kernel=row,
        run_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=True,
        endpoint=ENDPOINT, whole_beta_jet_proved=True, coverage_added=0, shared_acceptance=False), indent=2) + '\n',
        HERE / 'beta-public-audit-kernel.log': log})
    print('Complete original C beta jet against its literal specification recursively kernel-checked', flush=True)


def check():
    bound()
    r = json.loads((HERE / 'CHECKED.json').read_text())
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] or r['kernel']['command'] != kernel_command() or
            r['run_sha256'] != s.sha((HERE / 'RUN.json').read_bytes()) or
            r['kernel']['log_sha256'] != s.sha((HERE / 'beta-public-audit-kernel.log').read_bytes()) or
            (HERE / 'beta-public-audit-kernel.log').read_bytes() != (WORK / 'beta-public-audit-kernel.log').read_bytes()):
        raise ValueError('beta public completed kernel evidence differs')
    s.kernel.kernel((HERE / 'beta-public-audit-kernel.log').read_text(),
        sorted((WORK / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact complete-beta proof sources/objects/reports/kernel evidence verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py compile|kernel|check')
    {'compile': compile, 'kernel': kernel, 'check': check}[sys.argv[1]]()
