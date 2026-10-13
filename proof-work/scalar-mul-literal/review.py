"""Review frozen literal multiplication/write evidence; never accept public coverage."""
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
    if any(receipt[k] for k in ['full_acceptance', 'public_jet_equivalence',
                                'public_reader_calls_composed', 'public_wrapper_cleanup',
                                'second_operand_freeable_postcondition', 'square_shared_input_alias']):
        raise ValueError('literal helper/write chain is not public/square acceptance')
    if receipt['checkout_coverage_added'] != 0:
        raise ValueError('helper/write proof adds no public jet coverage')
    if not all(receipt[k] for k in ['actual_multiply_and_writer_calls',
                                    'literal_canonical_output_encoding',
                                    'writer_entry_representation_derived',
                                    'writer_post_multiply_invariant_derived']):
        raise ValueError('checked composition boundary drift')


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(report, expected):
    if '...' in report or re.findall(r'(?m)^PUBLIC_CHAIN_(TYPE|DEF) (\S+)$', report) != expected:
        raise ValueError('truncated, missing, duplicate or reordered contract')


def dependencies(entries):
    inherited = {'ClassicalDedekindReals.sig_forall_dec',
                 'ClassicalDedekindReals.sig_not_dec', 'Classical_Prop.classic',
                 'FunctionalExtensionality.functional_extensionality_dep'}
    representation = {'four_words_scalar_at', 'scalar_mul_output_owned',
                      'scalar_writer_initial_rep_from_mul', 'scalar_mul_initial_rep_from_storage'}
    numeric = {'canonical_scalar_multiply_numeric', 'canonical_scalar_multiply_normalized_value'}
    expected = {}
    for entry in entries:
        for name in entry['results']:
            expected[entry['module'] + '.' + name] = (
                inherited | {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                if name.startswith('eval_') else inherited if name in representation else
                {'FunctionalExtensionality.functional_extensionality_dep'} if name in numeric else set())
    return expected


def assumptions(report, expected):
    common = load('literal_assumption_common', ARCHIVE.parent / 'scalar-mul/review.py')
    try:
        return common.assumptions(report, expected)
    except KeyError as error:
        raise ValueError('orphan assumption record') from error


def review():
    parent = load('literal_caller_function', ARCHIVE.parent / 'scalar-mul-function/review.py')
    if parent.review()['results'] != 16:
        raise ValueError('checked original function prerequisite drift')
    common = load('literal_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    scanner = load('literal_scanner', base / 'scan-jet-proofs.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (6, 17, 2):
        raise ValueError('unexpected literal call-chain closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log drift: ' + name)
    for name in ['public_assumptions.v', 'public_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('audit driver drift')
    if any((work / name).read_bytes() for name in
           ['public_build.log', 'public_assumptions.err', 'public_contracts.err']):
        raise ValueError('compiler diagnostics')
    checked = assumptions((work / 'public_assumptions.out').read_text(), dependencies(manifest['modules']))
    if sum(not ds for ds in checked.values()) != 7:
        raise ValueError('closed-result classification drift')
    contracts((work / 'public_contracts.out').read_text(),
              [('TYPE', name) for name in results] + [('DEF', name) for name in definitions])
    common.kernel((work / 'public_kernel_600.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('literal_audit', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency fingerprint drift')
    reuse = manifest['reused_writer']
    if digest(Path(reuse['source'])) != reuse['sha256']:
        raise ValueError('reused scalar-add writer source drift')
    if digest(work / 'jet_secp_scalar_writer_word.v') != reuse['sha256']:
        raise ValueError('generic writer not reused byte-for-byte')
    return {'modules': 6, 'results': 17, 'closed_results': 7, 'definitions': 2,
            'exact_dependencies_and_kernel_context_match': True,
            'actual_multiply_and_writer_calls': True,
            'literal_canonical_output_encoding': True,
            'writer_representation_and_post_multiply_invariant_derived': True,
            'generic_scalar_add_writer_reused_exactly': True,
            'public_reader_calls_composed': False, 'public_wrapper_cleanup': False,
            'second_operand_freeable_postcondition': False,
            'square_shared_input_alias': False, 'public_jet_equivalence': False,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
