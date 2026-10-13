"""Check lambda fresh-frame and initialized local contracts, not registration."""
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


shared = load('lambda_frames_shared', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest = shared.digest
FULL = shared.CLASSICAL | shared.SEMANTICS | {
    'Events.external_functions_properties', 'Events.inline_assembly_properties'}
CLOSED = {'z_of_bits_testbit', 'z_of_bits_range', 'packed_word_testbit',
          'input_run_length', 'nth_error_repeat_in'}
EXECUTION = {'scalar_lambda_runs_from_initialized', 'scalar_lambda_runs_from_actual_init',
             'scalar_lambda_initialized_local_spec'}


def terminal(receipt):
    for kind in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[kind]['exit_code'] != 0:
            raise ValueError('failed/nonterminal evidence')
    for key in ['actual_secp_initialization_exists', 'all_inputs_fresh_frames',
                'literal_original_call', 'initialized_local_contract', 'startup_preserved']:
        if not receipt[key]:
            raise ValueError('missing proved boundary: ' + key)
    if (receipt['normal_registration'] or receipt['full_acceptance']
            or receipt['checkout_coverage_added'] or receipt['c_evaluator_setup_proved']):
        raise ValueError('scratch proof is not registration/acceptance or C evaluator setup')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^LAMBDA_FRAMES_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered records')


def definition(source, name):
    match = re.search(r'\bDefinition\s+' + name + r'\b.*? :=(.*?)\.\s*(?:$|\n)', source, re.S)
    if not match:
        raise ValueError('missing definition: ' + name)
    return re.sub(r'\s+', '', match[1])


def boundary(contract, legacy, fresh, local, state):
    # Apart from added Ready entry/postconditions, all old outputs/framing remain exact.
    new = definition(contract, 'secp_jet_initialized_local_spec')
    old = definition(legacy, 'secp_jet_local_spec')
    if not new.startswith('forall') or new.count('Readym->') != 1 or not new.endswith('/\\Readymf'):
        raise ValueError('initialized-state boundary changed')
    if new.replace('Readym->', '', 1).removesuffix('/\\Readymf') != old:
        raise ValueError('legacy frame/output contract changed')
    compact = lambda s: re.sub(r'\s+', '', s)
    required = [
        'secp_jet_initialized_local_spec scalar_lambda_initialized f_simplicity_scalar_multiply_lambda (Word 8) (Word 8)',
        '(@canonical_scalar_multiply_lambda Alg.CoreFunSem)',
        'eval_secp_scalar_lambda_initialized env m bd dbase bs sbase bw outedge cursor 256 bi edge rc a',
    ]
    if any(compact(n) not in compact(local) for n in required):
        raise ValueError('literal original-function public contract changed')
    required_fresh = [
        'Theorem scalar_lambda_runs_from_actual_init (value : Ty.tySem (Word 8)) env :',
        'Genv.init_mem jets_secp.prog = Some mi /\\ scalar_lambda_initialized mi',
        'destruct scalar_lambda_initialized_memory_exists',
        'jet_frames_constructible m0 (encode value) 256',
        'scalar_lambda_initialized_old_blocks',
        'Clight2.eval_funcall secp_ge m (Internal f_simplicity_scalar_multiply_lambda)',
        'finv m bd 0 bw 0 256 256 bi mf true (encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value))',
        'scalar_lambda_initialized mf',
        'Mem.valid_block mi b -> Mem.load chunk mf b ofs = Mem.load chunk mi b ofs',
    ]
    if any(compact(n) not in compact(fresh) for n in required_fresh):
        raise ValueError('fresh actual-startup/original-call/literal-output boundary changed')
    # Constructor promises backwards permissions only; derive final readability from real loads.
    required_state = ['Mem.perm m\' b ofs k p -> Mem.perm m b ofs k p',
                      'scalar_lambda_words_readable m\' scalar_lambda_block HL\'',
                      'apply (proj1 (HB ofs k p))', 'Mem.perm_cur_max']
    if any(compact(n) not in compact(state) for n in required_state):
        raise ValueError('readonly preservation bridge changed')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    load('frames_startup_parent', ARCHIVE.parent / 'scalar-lambda-startup/review.py').review()
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    scanner = load('frames_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = scanner.code_only(path.read_text())
        if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
                or re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', source, re.M) != entry['definitions']):
            raise ValueError('source inventory changed')
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', source):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (5, 16, 7):
        raise ValueError('unexpected closure')
    if digest(ARCHIVE / 'jet_frame_constructible.v.source') != manifest['reused_constructor_sha256']:
        raise ValueError('reused constructor changed')
    boundary((ARCHIVE / 'jet_secp_initialized_contract.v.source').read_text(),
             (base / 'C/jet_secp_normalize_local.v').read_text(),
             (ARCHIVE / 'jet_secp_scalar_lambda_fresh.v.source').read_text(),
             (ARCHIVE / 'jet_secp_scalar_lambda_local.v.source').read_text(),
             (ARCHIVE / 'jet_secp_scalar_lambda_frame_state.v.source').read_text())
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/object/driver/log drift: ' + name)
    for kind in ['assumptions', 'contracts']:
        name = 'lambda_frames_' + kind + '.v'
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
        if (work / ('lambda_frames_' + kind + '.err')).read_bytes():
            raise ValueError('compiler diagnostics')
    normal = load('frames_deps', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    parsed = normal.assumptions((work / 'lambda_frames_assumptions.out').read_text())
    expected = {n: set() if n.split('.')[-1] in CLOSED else
                FULL if n.split('.')[-1] in EXECUTION else shared.CLASSICAL for n in results}
    if parsed != expected:
        raise ValueError('exact per-result dependency set changed')
    contracts((work / 'lambda_frames_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    common = load('frames_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'lambda_frames_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('frames_base', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable base drift')
    return {'modules': 5, 'results': 16, 'closed_results': 5, 'definitions': 7,
            'all_inputs_fresh_frames': True, 'initialized_local_contract': True,
            'startup_preserved': True, 'c_evaluator_setup_proved': False,
            'normal_registration': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))

