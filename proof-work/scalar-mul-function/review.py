"""Review frozen whole scalar_mul function evidence; never accepts public jet coverage."""
import hashlib
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


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def terminal(receipt):
    if any(receipt[k]['exit_code'] != 0 for k in ['build', 'kernel']):
        raise ValueError('failed or nonterminal verification')
    if (receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0
            or receipt['public_jet_equivalence'] or receipt['square_shared_input_alias']):
        raise ValueError('whole in-place caller is not public/square acceptance')
    if not receipt['original_scalar_mul_function_entry_alloc_free'] or not receipt['r_equals_a']:
        raise ValueError('caller boundary or actual alias claim drift')


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^BOUNDARY_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated, missing, duplicate or reordered contract')


def dependencies(entries):
    inherited = {'ClassicalDedekindReals.sig_forall_dec',
                 'ClassicalDedekindReals.sig_not_dec', 'Classical_Prop.classic',
                 'FunctionalExtensionality.functional_extensionality_dep'}
    expected = {}
    for entry in entries:
        for name in entry['results']:
            expected[entry['module'] + '.' + name] = (
                inherited | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                if name.startswith('eval_scalar_mul_caller_') else inherited
                if name in {'scalar_mul_inputs_valid', 'scalar_mul_stack_cell_reindex',
                            'scalar_mul_stack_rotate', 'scalar_mul_caller_allocates'} else set())
    return expected


def assumptions(text, expected):
    common = load('boundary_assumption_common', ARCHIVE.parent / 'scalar-mul/review.py')
    try:
        return common.assumptions(text, expected)
    except KeyError as error:
        raise ValueError('orphan assumption record') from error


def review():
    parent = load('boundary_caller_body', ARCHIVE.parent / 'scalar-mul-caller/review.py')
    if parent.review()['results'] != 22:
        raise ValueError('checked body/current-memory prerequisite drift')
    common = load('boundary_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    scanner = load('boundary_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text()
        inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('skipped or assumed proof')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (3, 16, 7):
        raise ValueError('unexpected caller function closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['boundary_assumptions.v', 'boundary_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in
           ['boundary_build.log', 'boundary_assumptions.err', 'boundary_contracts.err']):
        raise ValueError('compiler diagnostics')
    checked = assumptions((work / 'boundary_assumptions.out').read_text(), dependencies(manifest['modules']))
    if sum(not ds for ds in checked.values()) != 10:
        raise ValueError('closed-result classification drift')
    contracts((work / 'boundary_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    common.kernel((work / 'boundary_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('boundary_audit', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    return {'modules': 3, 'results': 16, 'closed_results': 10, 'definitions': 7,
            'exact_dependencies_and_kernel_context_match': True,
            'complete_original_scalar_mul_function_entry_alloc_free': True,
            'r_equals_a': True, 'fresh_uninitialized_product_array': True,
            'actual_four_post_free_output_loads': True,
            'exact_product_modulo_canonical_order': True,
            'outside_both_operand_regions_framing': True,
            'square_shared_input_alias': False, 'public_jet_equivalence': False,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
