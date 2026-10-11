"""Read-only original reduce512 execution evidence; not canonical equivalence."""
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def terminal(receipt):
    if any(receipt[k]['exit_code'] != 0 for k in ['build', 'kernel', 'drivers']):
        raise ValueError('failed/nonterminal verification')
    if receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('execution helper is not public equivalence acceptance')


def inventory(text, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
            or re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', text, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^REDUCE512_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicate contract')


def review():
    parent = load('reduce512_product_reference', ARCHIVE.parent / 'scalar-mul512/review-product.py')
    if parent.review()['new_results'] != 50:
        raise ValueError('compact executor/product prerequisite drift')
    common = load('reduce512_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if common.digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        inventory(path.read_text(), entry)
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (3, 13, 5):
        raise ValueError('unexpected execution closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['reduce512_assumptions.v', 'reduce512_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['reduce512_assumptions.err', 'reduce512_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    expected = {n: set(deps) if n in receipt['execution_results'] else set() for n in results}
    actual = common.assumptions((work / 'reduce512_assumptions.out').read_text(), expected)
    contracts((work / 'reduce512_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    return {'modules': 3, 'results': 13, 'closed_results': sum(not x for x in actual.values()),
            'definitions': 5, 'original_reduce512_call': True,
            'allocation_free_and_current_limb_loads': True,
            'shift64_execution_oracle_already_proved': True,
            'only_original_owned_representation_premise': True,
            'all_contracts_untruncated': True, 'source_driver_dependency_kernel_evidence_matches': True,
            'numeric_modulo_order_identity': False, 'public_jet_equivalence': False,
            'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
