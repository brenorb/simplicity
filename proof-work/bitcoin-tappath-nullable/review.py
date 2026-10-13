"""Read-only review of the nullable tappath candidate; never accepts registry changes."""
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
        raise ValueError('nonterminal or failed verification')
    if receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('candidate is not registered acceptance or new coverage')


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^NULLABLE_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated, missing, duplicate or reordered contract')


def assumptions(text, expected):
    common = load('nullable_assumption_common', ARCHIVE.parent / 'scalar-mul/review.py')
    try:
        return common.assumptions(text, expected)
    except KeyError as error:
        raise ValueError('orphan assumption record') from error


def review():
    common = load('nullable_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    results, definitions = [], []
    scanner = load('nullable_scanner', base / 'scan-jet-proofs.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (2, 9, 1):
        raise ValueError('unexpected nullable proof closure')
    for name, value in receipt['evidence_sha256'].items():
        if digest(work / name) != value:
            raise ValueError('source/compiled/driver/log evidence drift: ' + name)
    for name in ['nullable_assumptions.v', 'nullable_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    if any((work / name).read_bytes() for name in
           ['final_build.log', 'final_assumptions.err', 'final_contracts.err']):
        raise ValueError('compiler diagnostics')
    execution = {results[1], results[2]}
    closed = {results[5], results[6]}
    inherited = {'ClassicalDedekindReals.sig_forall_dec',
                 'ClassicalDedekindReals.sig_not_dec', 'Classical_Prop.classic',
                 'FunctionalExtensionality.functional_extensionality_dep'}
    expected = {name: set() if name in closed else inherited | (
        {'Events.external_functions_sem', 'Events.inline_assembly_sem'} if name in execution else set())
        for name in results}
    checked = assumptions((work / 'final_assumptions.out').read_text(), expected)
    contracts((work / 'final_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    common.kernel((work / 'final_kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    audit = load('nullable_audit', base / 'jet-audit-inputs.py')
    if audit.fingerprint(base, REPO) != manifest['dependency_fingerprint']:
        raise ValueError('immutable dependency source fingerprint drift')
    if manifest['modules'][0]['sha256'] != manifest['claude_source_sha256']:
        raise ValueError('Claude proof was not preserved exactly')
    return {'modules': 2, 'results': len(results), 'closed_results': sum(not d for d in checked.values()),
            'definitions': 1, 'exact_inherited_dependencies': True,
            'old_contract_implies_nullable': True, 'nonempty_contracts_equivalent': True,
            'empty_path_needs_no_path_pointer_load': True, 'old_contract_rejects_null': True,
            'original_C_to_raw_spec_candidate': True, 'full_acceptance': False,
            'registered_contract_updated': False, 'builder_chain_independently_checked_here': False,
            'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
