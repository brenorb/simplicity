"""Checked readable-rhs product/body evidence, not a public lambda theorem."""
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


shared = load('borrowed_shared_review', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest, inventory = shared.digest, shared.inventory
EXECUTION = {'BorrowC.jet_secp_scalar_mul512_borrowed.eval_scalar_mul512_borrowed',
             'BorrowC.jet_secp_scalar_mul512_borrowed.eval_scalar_mul512_borrowed_product',
             'BorrowC.jet_secp_borrowed_product_reduce.eval_borrowed_product_then_reduce',
             'BorrowC.jet_secp_scalar_mul_borrowed_body.exec_scalar_mul_borrowed_body'}
REPRESENTATION = {'BorrowC.jet_secp_borrowed_product_reduce.borrowed_product_reduce_entry_rep',
                  'BorrowC.jet_sx_region_lframe.region_ok_lframe',
                  'BorrowC.jet_secp_scalar_mul_borrowed_body.borrowed_rhs_disjoint',
                  'BorrowC.jet_secp_scalar_mul_borrowed_body.borrowed_rhs_after_reduce'}


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if (receipt['public_jet_equivalence'] or receipt['scalar_mul_function_entry_alloc_free']
            or receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0):
        raise ValueError('body/helper is not a complete function/public lambda theorem')
    if not receipt['readable_nonowned_rhs'] or not receipt['actual_original_scalar_mul_body']:
        raise ValueError('readable actual-body boundary missing')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^BORROWED_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered contract report')


def expected_dependencies(results):
    if not EXECUTION | REPRESENTATION <= set(results):
        raise ValueError('missing execution/representation theorem')
    return {name: shared.CLASSICAL | shared.SEMANTICS if name in EXECUTION else
            shared.CLASSICAL if name in REPRESENTATION else set() for name in results}


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text()); terminal(receipt)
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    parent_dir = ARCHIVE.parent / 'scalar-multiply-integration'
    load('borrowed_checked_parent', parent_dir / 'review-normal.py').review(parent_dir / 'ASSEMBLY.json')
    scanner = load('borrowed_scanner', base / 'scan-jet-proofs.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (4, 14, 4):
        raise ValueError('unexpected borrowed body closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['borrowed_assumptions.v', 'borrowed_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in ['borrowed_assumptions.err', 'borrowed_contracts.err']):
        raise ValueError('compiler diagnostics')
    normal = load('borrowed_dependencies', parent_dir / 'review-normal.py')
    checked = normal.assumptions((work / 'borrowed_assumptions.out').read_text())
    if checked != expected_dependencies(results) or sum(not deps for deps in checked.values()) != 6:
        raise ValueError('exact per-result dependencies changed')
    contracts((work / 'borrowed_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions])
    common = load('borrowed_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'borrowed_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('borrowed_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    return {'modules': 4, 'results': 14, 'closed_results': 6, 'definitions': 4,
            'readable_nonowned_rhs': True, 'fresh_uninitialized_product_buffer': True,
            'actual_eight_product_loads': True, 'rhs_preserved_through_reduction': True,
            'actual_original_scalar_mul_body': True, 'shared_region_lframe_lemma': True,
            'exact_dependencies_and_kernel_context_match': True,
            'contract_report_bytes': (work / 'borrowed_contracts.out').stat().st_size,
            'scalar_mul_function_entry_alloc_free': False, 'public_jet_equivalence': False,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
