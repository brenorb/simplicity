"""In-memory preservation checks for the cumulative main reconciliation plan."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('square_main_test', archive / 'plan-main.py')
plan = importlib.util.module_from_spec(spec); spec.loader.exec_module(plan)
if len(sys.argv) != 2:
    raise SystemExit('usage: test-plan.py FULL_PLAN.json')
data = json.loads(Path(sys.argv[1]).read_text()); plan.validate_preserving_plan(data)
count = 0
for key, value in [('source_conflicts', [{'path': 'C/existing.v'}]),
                   ('changed_existing_dependencies', {'old': ['new_axiom']}),
                   ('inherited_contract_bytes_identical', False),
                   ('inherited_contract_order_preserved', False),
                   ('missing_contract_records', ['old']), ('kernel_allowlist_identical', False),
                   ('writes_performed', True), ('checkout_coverage_added', 1)]:
    bad = copy.deepcopy(data); bad[key] = value
    try:
        plan.validate_preserving_plan(bad)
    except ValueError:
        count += 1
    else:
        raise AssertionError('unsafe proposal accepted: ' + key)
for key, value in [('main_rows_preserved_in_order', False), ('main_rows_missing', ['existing']),
                   ('main_is_byte_prefix', False)]:
    bad = copy.deepcopy(data); bad['inventory_extensions']['_CoqProject'][key] = value
    try:
        plan.validate_preserving_plan(bad)
    except ValueError:
        count += 1
    else:
        raise AssertionError('discarded inventory accepted')
for changed in ['../outside.v', '/absolute.v', 'C//ambiguous.v']:
    bad = copy.deepcopy(data); bad['new_source_files'][0]['path'] = changed
    try:
        plan.validate_preserving_plan(bad)
    except ValueError:
        count += 1
    else:
        raise AssertionError('unsafe source path accepted')
bad = copy.deepcopy(data); bad['asset_conflicts_to_review'].append(
    {'path': 'unrelated.py', 'explicit_gate_review': False})
try:
    plan.validate_preserving_plan(bad)
except ValueError:
    count += 1
else:
    raise AssertionError('unreviewed asset conflict accepted')
print(f'main reconciliation: positive fixture and {count} unsafe proposals rejected; no audit/main inputs changed')
