"""In-memory contract/status mutations; never alter proof or audit inputs."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
path = Path(__file__).with_name('review.py')
spec = importlib.util.spec_from_file_location('review', path)
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
assert review.review()['closed_results'] == 9
text = 'ACCUM_TYPE M.a\na : nat\nACCUM_DEF M.b\nb = O\n'
inventory = [('TYPE', 'M.a'), ('DEF', 'M.b')]
review.contracts(text, inventory)
bad_reports = [text.replace('ACCUM_DEF M.b\nb = O\n', ''),
               text + 'ACCUM_TYPE M.a\na : nat\n', text.replace('a : nat', '...'),
               text.replace('ACCUM_TYPE M.a', 'ACCUM_TYPE M.other')]
for bad in bad_reports:
    try:
        review.contracts(bad, inventory)
    except ValueError:
        continue
    raise AssertionError('contract drift accepted')
receipt = json.loads((path.parent / 'REVIEW.json').read_text())
for target in ['builds', 'kernel', 'drivers']:
    bad = copy.deepcopy(receipt)
    (bad[target][0] if target == 'builds' else bad[target])['exit_code'] = 1
    try:
        review.terminal(bad)
    except ValueError:
        continue
    raise AssertionError('failed verification accepted')
print('multiply-accumulate review passed; seven in-memory contract/terminal-status mutations rejected')
