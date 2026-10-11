"""Read-only exact eight-limb C helper review; no public jet registration."""
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
        raise ValueError('helper is not public jet acceptance')


def inventory(source, entry):
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', source, re.M) != entry['results']
            or re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', source, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^PRODUCT_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered contract')


def review():
    parent = load('product_low_evidence', ARCHIVE / 'review-low.py')
    if parent.review()['new_results'] != 6:
        raise ValueError('execution/value prerequisite drift')
    accum = load('product_accum_evidence', ARCHIVE.parent / 'scalar-mul-accum/review.py')
    if accum.review()['new_results'] != 11:
        raise ValueError('multiply-accumulate prerequisite drift')
    common = load('product_common_evidence', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'PRODUCT-REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    results, definitions = [], []
    for entry in receipt['modules']:
        source = ARCHIVE / (entry['file'] + '.source')
        if common.digest(source) != entry['sha256'] or source.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/source drift')
        inventory(source.read_text(), entry)
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(receipt['modules']), len(results), len(definitions)) != (6, 50, 42):
        raise ValueError('unexpected full-product closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['mul512_product_assumptions.v', 'mul512_product_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['mul512_product_assumptions.err', 'mul512_product_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    root = 'MulC.jet_secp_scalar_mul512_owned_product.eval_scalar_mul512_owned_product'
    expected = {n: set(deps) if n == root else set() for n in results}
    actual = common.assumptions((work / 'mul512_product_assumptions.out').read_text().replace(
        'PRODUCT_ASSUMPTIONS ', 'JET_ASSUMPTIONS '), expected)
    contracts((work / 'mul512_product_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    return {'modules': 6, 'new_results': 50, 'closed_results': sum(not d for d in actual.values()),
            'definitions': 42, 'full_512_bit_product': True,
            'all_eight_current_memory_limb_loads': True,
            'root_premise': 'original owned input representation only',
            'all_contracts_untruncated': True,
            'source_driver_dependency_kernel_evidence_matches': True,
            'public_jet_equivalence': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
