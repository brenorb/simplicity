"""Audit the original lambda call and its explicit, initialized-memory boundary."""
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


shared = load('lambda_caller_shared', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest, inventory = shared.digest, shared.inventory


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if not receipt['complete_original_public_funcall'] or not receipt['startup_state_preserved']:
        raise ValueError('complete original call/startup boundary missing')
    if (receipt['normal_registration'] or receipt['full_acceptance'] or receipt['checkout_coverage_added']
            or receipt['init_mem_existence_proved']):
        raise ValueError('scratch initialized-memory result is not normal/caller acceptance')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^LAMBDA_CALLER_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered report')


def call_boundary(sources):
    compact = lambda s: re.sub(r'\s+', '', s)
    ready = compact(sources['jet_secp_scalar_lambda_initialized.v'])
    life = compact(sources['jet_secp_scalar_lambda_lifecycle.v'])
    rest = compact(sources['jet_secp_scalar_lambda_rest.v'])
    frame = compact(sources['jet_clight_readonly_frame.v'])
    needed = [
        r'Definition scalar_lambda_initialized (m : Mem.mem) : Prop := scalar_lambda_global_rep m /\ readonly_region_bounds m scalar_lambda_block 0 32.',
        'Clight2.eval_funcall secp_ge m0 (Ctypes.Internal f_simplicity_scalar_multiply_lambda)',
        'encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value)',
        r'lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf /\ scalar_lambda_initialized mf.',
        'Genv.init_mem jets_secp.prog = Some m -> scalar_lambda_initialized m.',
    ]
    if any(compact(x) not in ready for x in needed):
        raise ValueError('initialized call uses a different function/spec/output/startup boundary')
    if 'scalar_free_public_locals' not in life or 'exactHFree.' not in life:
        raise ValueError('real private-local cleanup removed')
    if 'eapply eval_Evar_global; [reflexivity|exact scalar_lambda_global_symbol]' not in sources['jet_secp_scalar_lambda_rest.v']:
        raise ValueError('global rhs replaced by a local/shared input')
    if compact('Vptr scalar_lambda_block Ptrofs.zero') not in rest:
        raise ValueError('original borrowed global argument missing')
    if compact('readonly_region_bounds m b lo hi') not in frame or compact('Mem.range_perm mf b lo hi Cur Readable') not in frame:
        raise ValueError('readback incorrectly promises unconditional survival')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    load('lambda_caller_parent', ARCHIVE.parent / 'scalar-lambda/review.py').review()
    base = Path(manifest['dependency_coq']); work = Path(manifest['scratch']['caller'])
    scanner = load('lambda_caller_scanner', base / 'scan-jet-proofs.py')
    results, definitions, sources = [], [], {}
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        live = Path(manifest['scratch'][entry['group']]) / entry['file']
        if digest(path) != entry['sha256'] or path.read_bytes() != live.read_bytes():
            raise ValueError('source/compiled archive drift')
        source = path.read_text(); sources[entry['file']] = source; inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (11, 53, 7):
        raise ValueError('unexpected caller closure')
    call_boundary(sources)
    if sources['jet_clight_forward.v'] != (ARCHIVE.parent / 'sha-support/jet_clight_forward.v.source').read_text():
        raise ValueError('borrowed shared forward lemma changed')
    for group, entries in receipt['evidence_sha256'].items():
        directory = Path(manifest['scratch'][group])
        for name, value in entries.items():
            if digest(directory / name) != value:
                raise ValueError('source/object/driver/log drift: ' + name)
    for name in ['lambda_caller_assumptions.v', 'lambda_caller_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / ('lambda_caller_' + n + '.err')).read_bytes() for n in ['assumptions', 'contracts']):
        raise ValueError('driver diagnostics')
    normal = load('lambda_caller_deps', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    parsed = normal.assumptions((work / 'lambda_caller_assumptions.out').read_text())
    expected = {n: set(ds) for n, ds in receipt['reviewed_dependencies'].items()}
    if set(expected) != set(results) or parsed != expected:
        raise ValueError('exact reviewed per-result dependencies changed')
    contracts((work / 'lambda_caller_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    common = load('lambda_caller_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'lambda_caller_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('lambda_caller_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable base drift')
    return {'modules': 11, 'results': 53, 'closed_results': sum(not ds for ds in parsed.values()),
            'definitions': 7, 'complete_original_public_funcall': True, 'literal_output': True,
            'actual_entry_copy_helpers_return_free': True, 'startup_state_preserved': True,
            'startup_state_required': True, 'normal_registration': False, 'full_acceptance': False,
            'init_mem_existence_proved': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
