"""Read-only first-limb execution/value extension review, not public coverage."""
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


def review():
    parent = load('compact_evidence', ARCHIVE / 'review.py')
    if parent.review()['results'] != 19:
        raise ValueError('execution prerequisite drift')
    common = load('product_evidence', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'LOW-REVIEW.json').read_text())
    work = Path(manifest['scratch'])
    entry = receipt['module']
    source = ARCHIVE / (entry['file'] + '.source')
    if common.digest(source) != entry['sha256'] or source.read_bytes() != (work / entry['file']).read_bytes():
        raise ValueError('archive/source drift')
    text = source.read_text()
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
            or re.findall(r'^Definition\s+(\w+)', text, re.M) != entry['definitions']):
        raise ValueError('source inventory drift')
    results = [entry['name'] + '.' + n for n in entry['results']]
    definitions = [entry['name'] + '.' + n for n in entry['definitions']]
    if (len(results), len(definitions)) != (6, 2):
        raise ValueError('unexpected first-limb closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['mul512_low_assumptions.v', 'mul512_low_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['mul512_low_assumptions.err', 'mul512_low_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('driver diagnostics')
    if any(receipt[k]['exit_code'] != 0 for k in ['build', 'kernel', 'drivers']):
        raise ValueError('failed/nonterminal verification')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    expected = {n: set(deps) if n == entry['name'] + '.eval_scalar_mul512_owned_low_product'
                else set() for n in results}
    actual = common.assumptions((work / 'mul512_low_assumptions.out').read_text(), expected)
    report = (work / 'mul512_low_contracts.out').read_text()
    if ('...' in report or re.findall(r'(?m)^LOW_(TYPE|DEF) (\S+)$', report)
            != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('truncated/missing/reordered contract')
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel output drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    return {'new_results': 6, 'closed_results': sum(not d for d in actual.values()),
            'definitions': 2, 'execution_prerequisite_results_revalidated': 19,
            'first_limb_is_full_256_bit_input_product_modulo_2_64': True,
            'full_512_bit_product': False, 'public_jet_equivalence': False,
            'source_contract_dependency_kernel_evidence_matches': True, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
