"""Read-only helper evidence review and in-memory negative fixtures."""
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('review', Path(__file__).with_name('review.py'))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
assert review.review()['closed_results'] == 14

dependencies = {'M.a': set(), 'M.b': {'Inherited.axiom'}}
good = ('JET_ASSUMPTIONS M.a\nClosed under the global context\n'
        'JET_ASSUMPTIONS M.b\nAxioms:\nInherited.axiom : Prop\n')
review.assumptions(good, dependencies)
cases = [lambda: review.assumptions(good.replace('JET_ASSUMPTIONS M.a\nClosed under the global context\n', ''), dependencies),
         lambda: review.assumptions(good + 'JET_ASSUMPTIONS M.a\nClosed under the global context\n', dependencies),
         lambda: review.assumptions(good.replace('Inherited.axiom', 'New.oracle'), dependencies),
         lambda: review.assumptions(good.replace('Inherited.axiom : Prop\n', ''), dependencies)]
inventory = [('TYPE', 'M.a'), ('DEF', 'M.b')]
text = 'MUL_TYPE M.a\na : nat\nMUL_DEF M.b\nb = O\n'
review.contracts(text, inventory)
cases += [lambda: review.contracts(text.replace('MUL_DEF M.b\nb = O\n', ''), inventory),
          lambda: review.contracts(text + 'MUL_TYPE M.a\na : nat\n', inventory),
          lambda: review.contracts(text.replace('a : nat', '...'), inventory),
          lambda: review.contracts(text, list(reversed(inventory)))]
kernel_text = ('CONTEXT SUMMARY\n* Axioms:\n  Inherited.axiom\n'
               '* Constants/Inductives relying on type-in-type: <none>\n'
               '* Constants/Inductives relying on unsafe (co)fixpoints: <none>\n'
               '* Inductives whose positivity is assumed: <none>\n')
review.kernel(kernel_text, ['Inherited.axiom'])
cases += [lambda: review.kernel(kernel_text.replace('CONTEXT SUMMARY', ''), ['Inherited.axiom']),
          lambda: review.kernel(kernel_text.replace('Inherited.axiom', 'New.oracle'), ['Inherited.axiom']),
          lambda: review.kernel(kernel_text.replace('type-in-type: <none>', 'type-in-type: unsafe'), ['Inherited.axiom']),
          lambda: review.kernel(kernel_text.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: unsafe'), ['Inherited.axiom']),
          lambda: review.kernel(kernel_text.replace('positivity is assumed: <none>', 'positivity is assumed: unsafe'), ['Inherited.axiom'])]
for case in cases:
    try:
        case()
    except ValueError:
        continue
    raise AssertionError('negative fixture accepted')
print(f'helper source/evidence review and {len(cases)} in-memory dependency/contract/kernel drift fixtures passed')
