"""In-memory negative evidence checks; no source or compiled inputs changed."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rejected(label, action):
    try:
        action()
    except ValueError:
        return
    raise AssertionError('mutation accepted: ' + label)


review = load('product_review', archive / 'review-product.py')
common = load('product_common', archive.parent / 'scalar-mul/review.py')
receipt = json.loads((archive / 'PRODUCT-REVIEW.json').read_text())
manifest = json.loads((archive / 'manifest.json').read_text())
work = Path(manifest['scratch'])
assert review.review()['closed_results'] == 49
for key in ['build', 'kernel', 'drivers']:
    changed = copy.deepcopy(receipt)
    changed[key]['exit_code'] = None
    rejected(key + ' nonterminal', lambda: review.terminal(changed))
changed = copy.deepcopy(receipt)
changed['checkout_coverage_added'] = 1
rejected('unearned public coverage', lambda: review.terminal(changed))
entry = receipt['modules'][0]
source = (archive / (entry['file'] + '.source')).read_text()
rejected('missing declaration', lambda: review.inventory(source.replace('Lemma ', 'Definition ', 1), entry))
results = [e['module'] + '.' + n for e in receipt['modules'] for n in e['results']]
definitions = [e['module'] + '.' + n for e in receipt['modules'] for n in e['definitions']]
expected = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
report = (work / 'mul512_product_contracts.out').read_text()
rejected('truncated report', lambda: review.contracts(report + '...', expected))
rejected('missing contract', lambda: review.contracts(report.replace('PRODUCT_TYPE ', 'OMITTED ', 1), expected))
deps = json.loads((archive.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
root = 'MulC.jet_secp_scalar_mul512_owned_product.eval_scalar_mul512_owned_product'
expected_deps = {n: set(deps) if n == root else set() for n in results}
text = (work / 'mul512_product_assumptions.out').read_text().replace('PRODUCT_ASSUMPTIONS ', 'JET_ASSUMPTIONS ')
rejected('added axiom', lambda: common.assumptions(text + '\nUnexpected.proof_escape : True\n', expected_deps))
inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
kernel = (work / receipt['kernel']['log']).read_text()
rejected('unsafe kernel', lambda: common.kernel(kernel.replace('type-in-type: <none>', 'type-in-type: injected'), inherited))
print('full-product review passed; nine in-memory status/source/contract/dependency/kernel mutations rejected')
