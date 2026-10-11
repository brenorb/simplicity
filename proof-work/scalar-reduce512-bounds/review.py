"""Read-only evidence for the first-fold bounds and actual second prefix; no public acceptance."""
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
        raise ValueError('first-fold helper is not public equivalence acceptance')


def inventory(text, entry):
    explicit = [n for n in entry['definitions'] if n not in entry['generated_definitions']]
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
            or re.findall(r'^(?:Definition|Fixpoint|Record|Inductive)\s+(\w+)', text, re.M) != explicit):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^FOLD_BOUNDS_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicate contract')


def review():
    parent = load('fold_bounds_execution_reference', ARCHIVE.parent / 'scalar-reduce512-first/review.py')
    if parent.review()['results'] != 49:
        raise ValueError('original execution prerequisite drift')
    common = load('fold_bounds_common', ARCHIVE.parent / 'scalar-mul/review.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (2, 14, 12):
        raise ValueError('unexpected first-fold closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['fold_bounds_assumptions.v', 'fold_bounds_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['fold_bounds_assumptions.err', 'fold_bounds_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    actual = common.assumptions((work / 'fold_bounds_assumptions.out').read_text(), {n: set() for n in results})
    contracts((work / 'fold_bounds_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    return {'modules': 2, 'results': 14, 'closed_results': sum(not x for x in actual.values()),
            'definitions': 12, 'exact_delta_identity_and_sharp_first_high_bound': True,
            'second_fold_integer_bridge_bound': True, 'second_fold_actual_prefix_run': True,
            'second_fold_complete_source_value_binding': False,
            'whole_reduce512_numeric_modulo_identity': False,
            'public_jet_equivalence': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
