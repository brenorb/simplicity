"""Review the real shared-input scalar_mul boundary, not a public square jet."""
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
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


body = load('square_function_body_review', ARCHIVE.parent / 'scalar-square-alias/review.py')
digest, inventory = body.digest, body.inventory
EXECUTION = {'SqrFC.jet_secp_scalar_square_caller_function.eval_scalar_square_caller_inplace',
             'SqrFC.jet_secp_scalar_square_caller_observed.eval_scalar_square_caller_inplace_observed'}
REPRESENTATION = {'SqrFC.jet_secp_scalar_square_caller_alloc.' + name for name in
                  ['scalar_square_inputs_valid', 'scalar_square_stack_rotate', 'scalar_square_caller_allocates']}


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if receipt['public_jet_equivalence'] or receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('internal function is not public square acceptance')
    if not receipt['scalar_mul_function_entry_alloc_free'] or not receipt['actual_r_equals_a_equals_b']:
        raise ValueError('real shared-input function boundary missing')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^SQUARE_FUNCTION_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered contract report')


def expected_dependencies(results):
    if not (EXECUTION | REPRESENTATION) <= set(results):
        raise ValueError('missing execution/representation result')
    return {name: body.CLASSICAL | body.SEMANTICS if name in EXECUTION else
            body.CLASSICAL if name in REPRESENTATION else set() for name in results}


def review():
    if body.review()['results'] != 22:
        raise ValueError('checked shared-pointer body prerequisite changed')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    scanner = load('square_function_scanner', base / 'scan-jet-proofs.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (3, 9, 5):
        raise ValueError('unexpected function closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['square_function_assumptions.v', 'square_function_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in ['square_function_assumptions.err', 'square_function_contracts.err']):
        raise ValueError('compiler diagnostics')
    normal = load('square_function_dependencies', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    checked = normal.assumptions((work / 'square_function_assumptions.out').read_text())
    if checked != expected_dependencies(results) or sum(not ds for ds in checked.values()) != 4:
        raise ValueError('exact dependency sets changed')
    contracts((work / 'square_function_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions])
    common = load('square_function_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'square_function_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('square_function_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint changed')
    return {'modules': 3, 'results': 9, 'closed_results': 4, 'definitions': 5,
            'scalar_mul_function_entry_alloc_free': True, 'actual_r_equals_a_equals_b': True,
            'one_owned_input_region': True, 'actual_four_post_free_output_loads': True,
            'fresh_uninitialized_product_array': True, 'outside_input_framing': True,
            'exact_dependencies_and_kernel_context_match': True,
            'contract_report_bytes': (work / 'square_function_contracts.out').stat().st_size,
            'public_jet_equivalence': False, 'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
