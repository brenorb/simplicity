"""Review full internal scalar_mul with borrowed rhs; no public lambda claim."""
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


shared = load('borrowed_function_shared', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest, inventory = shared.digest, shared.inventory
EXECUTION = {'BorrowFC.jet_secp_scalar_mul_borrowed_function.eval_scalar_mul_borrowed_inplace',
             'BorrowFC.jet_secp_scalar_mul_borrowed_observed.eval_scalar_mul_borrowed_inplace_observed'}
CLOSED = {'BorrowFC.jet_secp_scalar_mul_borrowed_function.borrowed_stack_foot_cases'}


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if (receipt['public_jet_equivalence'] or receipt['full_acceptance']
            or receipt['checkout_coverage_added'] != 0):
        raise ValueError('internal function is not public lambda equivalence')
    for name in ['readable_nonowned_rhs', 'actual_original_scalar_mul_body',
                 'scalar_mul_function_entry_alloc_free', 'actual_output_loads_after_free']:
        if not receipt[name]:
            raise ValueError('actual borrowed function boundary missing: ' + name)


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^BORROWED_FUNCTION_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered contract report')


def expected_dependencies(results):
    if not EXECUTION | CLOSED <= set(results):
        raise ValueError('missing full function/output/closed theorem')
    return {name: shared.CLASSICAL | shared.SEMANTICS if name in EXECUTION else
            set() if name in CLOSED else shared.CLASSICAL for name in results}


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    load('borrowed_function_parent', ARCHIVE.parent / 'scalar-mul-borrowed/review.py').review()
    scanner = load('borrowed_function_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text(); inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + name for name in entry['results']]
        definitions += [entry['module'] + '.' + name for name in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (3, 7, 2):
        raise ValueError('unexpected complete borrowed function closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['borrowed_function_assumptions.v', 'borrowed_function_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in
           ['borrowed_function_assumptions.err', 'borrowed_function_contracts.err']):
        raise ValueError('compiler diagnostics')
    parent = ARCHIVE.parent / 'scalar-multiply-integration'
    normal = load('borrowed_function_dependencies', parent / 'review-normal.py')
    checked = normal.assumptions((work / 'borrowed_function_assumptions.out').read_text())
    if checked != expected_dependencies(results) or sum(not deps for deps in checked.values()) != 1:
        raise ValueError('exact per-result dependencies changed')
    contracts((work / 'borrowed_function_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions])
    common = load('borrowed_function_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'borrowed_function_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('borrowed_function_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    return {'modules': 3, 'results': 7, 'closed_results': 1, 'definitions': 2,
            'readable_nonowned_rhs': True, 'actual_original_scalar_mul_body': True,
            'scalar_mul_function_entry_alloc_free': True, 'actual_output_loads_after_free': True,
            'rhs_region_preserved': True, 'exact_dependencies_and_kernel_context_match': True,
            'contract_report_bytes': (work / 'borrowed_function_contracts.out').stat().st_size,
            'public_jet_equivalence': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
