"""Check actual secp initialization existence, not normal jet acceptance."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


shared = load('startup_shared', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest = shared.digest


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if not receipt['actual_secp_initialization_exists'] or not receipt['initialized_lambda_witness']:
        raise ValueError('actual startup witness missing')
    if receipt['full_acceptance'] or receipt['normal_registration'] or receipt['checkout_coverage_added']:
        raise ValueError('startup constructibility is not registration/acceptance')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^LAMBDA_STARTUP_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered report')


def boundary(generic, concrete):
    compact = lambda s: re.sub(r'\s+', '', s)
    if any(compact(n) not in compact(generic) for n in
           ['apply Genv.init_mem_exists', 'initializer_alignedb_sound',
            'forallb (initializer_referenceb (Genv.globalenv p))']):
        raise ValueError('alignment/reference conditions not discharged by generic existence proof')
    required = [
        'Definition secp_initialization_succeeds : bool := program_initialization_okb jets_secp.prog.',
        'exists m, Genv.init_mem jets_secp.prog = Some m.',
        r'exists m, Genv.init_mem jets_secp.prog = Some m /\ scalar_lambda_initialized m.',
        'program_initialization_checked (Ctypes.program_of_program jets_secp.prog)',
        'apply scalar_lambda_initialized_from_init; exact HI',
    ]
    if any(compact(n) not in compact(concrete) for n in required):
        raise ValueError('actual original program/state witness changed')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    load('startup_caller_parent', ARCHIVE.parent / 'scalar-lambda-caller/review.py').review()
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    scanner = load('startup_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text()
        if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
                or re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', source, re.M) != entry['definitions']):
            raise ValueError('source inventory changed')
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (2, 6, 4):
        raise ValueError('unexpected startup closure')
    boundary((ARCHIVE / 'jet_program_initialization.v.source').read_text(),
             (ARCHIVE / 'jet_secp_scalar_lambda_init_exists.v.source').read_text())
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/object/driver/log drift: ' + name)
    for name in ['lambda_startup_assumptions.v', 'lambda_startup_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / ('lambda_startup_' + n + '.err')).read_bytes() for n in ['assumptions', 'contracts']):
        raise ValueError('compiler diagnostics')
    normal = load('startup_deps', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    parsed = normal.assumptions((work / 'lambda_startup_assumptions.out').read_text())
    state = 'LamInitC.jet_secp_scalar_lambda_init_exists.scalar_lambda_initialized_memory_exists'
    expected = {n: shared.CLASSICAL if n == state else set() for n in results}
    if parsed != expected or sum(not ds for ds in parsed.values()) != 5:
        raise ValueError('exact per-result dependencies changed')
    contracts((work / 'lambda_startup_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    common = load('startup_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'lambda_startup_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('startup_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable base drift')
    return {'modules': 2, 'results': 6, 'closed_results': 5, 'definitions': 4,
            'actual_secp_initialization_exists': True, 'initialized_lambda_witness': True,
            'normal_registration': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
