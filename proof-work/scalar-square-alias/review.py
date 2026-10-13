"""Review shared-input square helper evidence, never public jet acceptance."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent
REPRESENTATION = {'SqrC.jet_secp_square_product_reduce.square_product_reduce_entry_rep'}
EXECUTION = {
    'SqrC.jet_secp_scalar_square512_run.eval_scalar_square512_fresh',
    'SqrC.jet_secp_scalar_square512_product.eval_scalar_square512_fresh_product',
    'SqrC.jet_secp_square_product_reduce.eval_square_product_then_reduce',
    'SqrC.jet_secp_scalar_square_body.exec_scalar_square_product_call',
    'SqrC.jet_secp_scalar_square_body.exec_scalar_square_body_inplace',
}
CLASSICAL = {'Classical_Prop.classic',
             'FunctionalExtensionality.functional_extensionality_dep',
             'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec'}
SEMANTICS = {'Events.external_functions_sem', 'Events.inline_assembly_sem'}


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source declaration inventory changed')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^SQUARE_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/duplicate/reordered contract report')


def terminal(receipt):
    for name in ['build', 'assumptions', 'contracts', 'kernel']:
        if receipt[name]['exit_code'] != 0:
            raise ValueError('failed/nonterminal verification')
    if (receipt['public_jet_equivalence'] or receipt['full_acceptance']
            or receipt['checkout_coverage_added'] != 0 or receipt['scalar_mul_function_entry_alloc_free']):
        raise ValueError('helper evidence does not establish a public/function boundary')
    if not receipt['actual_shared_input_pointer'] or not receipt['actual_original_scalar_mul_body']:
        raise ValueError('actual shared-input body boundary missing')


def expected_dependencies(results):
    if not (EXECUTION | REPRESENTATION) <= set(results):
        raise ValueError('missing execution/representation result')
    return {name: CLASSICAL | SEMANTICS if name in EXECUTION else
            CLASSICAL if name in REPRESENTATION else set() for name in results}


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
    scanner = load('square_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text()
        inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('assumed/skipped proof')
        results += [entry['module'] + '.' + name for name in entry['results']]
        definitions += [entry['module'] + '.' + name for name in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (5, 22, 9):
        raise ValueError('unexpected closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['square_assumptions.v', 'square_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in ['square_assumptions.err', 'square_contracts.err']):
        raise ValueError('driver diagnostics')
    normal = load('square_assumptions', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
    checked = normal.assumptions((work / 'square_assumptions.out').read_text())
    if checked != expected_dependencies(results) or sum(not ds for ds in checked.values()) != 16:
        raise ValueError('exact per-result dependency sets changed')
    contracts((work / 'square_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions])
    common = load('square_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((work / 'square_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('square_inputs', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    return {'modules': 5, 'results': 22, 'closed_results': 16, 'definitions': 9,
            'actual_shared_input_pointer': True, 'single_owned_input_region': True,
            'fresh_uninitialized_product_buffer': True, 'actual_eight_product_loads': True,
            'actual_original_scalar_mul_body': True, 'checked_reduction_reused': True,
            'exact_dependencies_and_kernel_context_match': True,
            'contract_report_bytes': (work / 'square_contracts.out').stat().st_size,
            'scalar_mul_function_entry_alloc_free': False, 'public_jet_equivalence': False,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
