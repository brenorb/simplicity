"""In-memory inventory/status/dependency mutations; no proof input writes."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
path = Path(__file__).with_name('review.py')
spec = importlib.util.spec_from_file_location('compact_review', path)
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
assert review.review()['closed_results'] == 16
text = 'COMPACT_TYPE M.a\na : nat\nCOMPACT_DEF M.b\nb = O\n'
inventory = [('TYPE', 'M.a'), ('DEF', 'M.b')]
review.contracts(text, inventory)
bad_reports = [text.replace('COMPACT_DEF M.b\nb = O\n', ''),
               text + 'COMPACT_TYPE M.a\na : nat\n', text.replace('a : nat', '...'),
               text.replace('COMPACT_TYPE M.a', 'COMPACT_TYPE M.other')]
for bad in bad_reports:
    try:
        review.contracts(bad, inventory)
    except ValueError:
        continue
    raise AssertionError('contract drift accepted')
receipt = json.loads((path.parent / 'REVIEW.json').read_text())
for target in ['builds', 'kernel', 'drivers']:
    for bad_status in [1, None]:
        bad = copy.deepcopy(receipt)
        (bad[target][0] if target in ['builds', 'kernel'] else bad[target])['exit_code'] = bad_status
        try:
            review.terminal(bad)
        except ValueError:
            continue
        raise AssertionError('failed/nonterminal verification accepted')
common = review.load(path.parent.parent / 'scalar-mul/review.py')
try:
    common.assumptions('JET_ASSUMPTIONS M.a\nAxioms:\nnew_axiom : True\n', {'M.a': set()})
except ValueError:
    pass
else:
    raise AssertionError('new assumption accepted')
print('compact execution evidence passed; eleven contract/status/dependency mutations rejected')
