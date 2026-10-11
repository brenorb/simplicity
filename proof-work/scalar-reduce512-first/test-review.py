"""Negative fixtures mutate in memory only; keep verified sources immutable."""
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


def rejected(name, action):
    try:
        action()
    except ValueError:
        return
    raise AssertionError('mutation accepted: ' + name)


review = load('first_fold_review', archive / 'review.py')
common = load('first_fold_common_test', archive.parent / 'scalar-mul/review.py')
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text())
work = Path(manifest['scratch'])
assert review.review()['closed_results'] == 49
for key in ['build', 'kernel', 'drivers']:
    changed = copy.deepcopy(receipt)
    changed[key]['exit_code'] = None
    rejected('nonterminal ' + key, lambda: review.terminal(changed))
changed = copy.deepcopy(receipt)
changed['checkout_coverage_added'] = 1
rejected('unearned coverage', lambda: review.terminal(changed))
entry = manifest['modules'][0]
source = (archive / (entry['file'] + '.source')).read_text()
rejected('source inventory', lambda: review.inventory(source.replace('Lemma ', 'Definition ', 1), entry))
results = [e['module'] + '.' + n for e in manifest['modules'] for n in e['results']]
definitions = [e['module'] + '.' + n for e in manifest['modules'] for n in e['definitions']]
expected = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
text = (work / 'first_fold_contracts.out').read_text()
rejected('truncation', lambda: review.contracts(text + '...', expected))
rejected('omitted contract', lambda: review.contracts(text.replace('FIRST_FOLD_TYPE ', 'OMITTED ', 1), expected))
text = (work / 'first_fold_assumptions.out').read_text()
rejected('added axiom', lambda: common.assumptions(text + '\nAxioms:\nUnexpected.proof_escape : True\n', {n: set() for n in results}))
inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
kernel = (work / receipt['kernel']['log']).read_text()
rejected('unsafe kernel', lambda: common.kernel(kernel.replace('type-in-type: <none>', 'type-in-type: injected'), inherited))
print('first-fold review passed; nine in-memory status/source/contract/dependency/kernel mutations rejected')
