"""Verify a full public multiplication proof candidate, not registry acceptance."""
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
    if receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('isolated public proof is not main acceptance')
    if receipt['square_shared_input_alias'] or receipt['checked_public_candidates'] != 1:
        raise ValueError('multiplication is not square or helper-count coverage')
    for name in ['complete_original_public_function', 'public_reader_calls_composed',
                 'public_wrapper_entry_copy_return_free', 'both_operand_freeable_postcondition_derived',
                 'literal_canonical_output_encoding', 'public_c_to_literal_contract']:
        if not receipt[name]:
            raise ValueError('public boundary claim drift: ' + name)


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(report, expected):
    if '...' in report or re.findall(r'(?m)^MULTIPLY_(TYPE|DEF) (\S+)$', report) != expected:
        raise ValueError('truncated, missing, duplicate or reordered contract')


def dependencies(entries):
    inherited = {'ClassicalDedekindReals.sig_forall_dec',
                 'ClassicalDedekindReals.sig_not_dec', 'Classical_Prop.classic',
                 'FunctionalExtensionality.functional_extensionality_dep'}
    closed = {'scalar_mul_foot_blocks', 'scalar_multiply_body_eq',
              'scalar_multiply_helper_symbols', 'scalar_multiply_public_entry',
              'scalar_multiply_public_blocks', 'scalar_multiply_alloc_facts'}
    representation = {'scalar_mul_second_disjoint', 'scalar_mul_second_after_reduce',
                      'scalar_reader_final_inv_to_next_initial', 'scalar_at_lframe',
                      'scalar_preserved_across_other_read', 'scalar_multiply_free_locals'}
    return {entry['module'] + '.' + name:
            set() if name in closed else inherited if name in representation else
            inherited | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
            for entry in entries for name in entry['results']}


def assumptions(report, expected):
    common = load('public_multiply_assumptions', ARCHIVE.parent / 'scalar-mul/review.py')
    try:
        return common.assumptions(report, expected)
    except KeyError as error:
        raise ValueError('orphan assumption record') from error


def shared_readers(work, origin):
    support = 'jet_secp_scalar_add_reader_support.v'
    pair = 'jet_secp_scalar_add_two_reads.v'
    if (work / support).read_bytes() != (origin / support).read_bytes():
        raise ValueError('shared reader support not reused exactly')
    expected = (origin / pair).read_text().replace(
        'C.jet_secp_scalar_add_reader_support', 'OwnC.jet_secp_scalar_add_reader_support')
    expected = re.sub(r'^Print Assumptions.*\n', '', expected, flags=re.M)
    if (work / pair).read_text().strip() != expected.strip():
        raise ValueError('two-reader port changed beyond namespace/audit footer')


def review():
    parent = load('public_multiply_literal_parent', ARCHIVE.parent / 'scalar-mul-literal/review.py')
    if parent.review()['results'] != 17:
        raise ValueError('checked arithmetic/literal/writer prerequisite drift')
    common = load('public_multiply_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    if manifest['full_acceptance'] or manifest['checkout_coverage_added'] or manifest['public_candidates'] != 1:
        raise ValueError('manifest incorrectly promotes coverage')
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    scanner = load('public_multiply_scanner', base / 'scan-jet-proofs.py')
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        source = path.read_text()
        inventory(source, entry)
        if re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b', scanner.code_only(source)):
            raise ValueError('skipped or assumed proof')
        results += [entry['module'] + '.' + name for name in entry['results']]
        definitions += [entry['module'] + '.' + name for name in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (14, 29, 6):
        raise ValueError('unexpected public proof closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['multiply_assumptions.v', 'multiply_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('audit driver drift')
    if any((work / name).read_bytes() for name in
           ['multiply_build.log', 'multiply_final_build.log',
            'multiply_final_assumptions.err', 'multiply_final_contracts.err']):
        raise ValueError('compiler diagnostics')
    checked = assumptions((work / 'multiply_final_assumptions.out').read_text(), dependencies(manifest['modules']))
    if sum(not ds for ds in checked.values()) != 6:
        raise ValueError('closed-result classification drift')
    contracts((work / 'multiply_final_contracts.out').read_text(),
              [('TYPE', name) for name in results] +
              [('DEF', name) for name in definitions + manifest['critical_definitions']])
    common.kernel((work / 'multiply_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('public_multiply_audit', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    shared_readers(work, Path(manifest['shared_reader_origin']))
    return {'modules': 14, 'results': 29, 'closed_results': 6, 'new_definitions': 6,
            'critical_definitions': 3, 'exact_dependencies_and_kernel_context_match': True,
            'complete_original_public_scalar_multiply_contract': True,
            'literal_canonical_specification_unchanged': True,
            'readers_entry_copy_return_and_all_frees_derived': True,
            'both_operand_freeable_postcondition_derived': True,
            'shared_readers_reused': True, 'checked_public_candidates': 1,
            'square_shared_input_alias': False, 'full_acceptance': False,
            'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
