"""Read-only reconciliation; neither installs sources nor accepts a candidate.

Reuse the earlier exact source/inventory/index comparison and the multiply
reviewer's ordered contract parser (including its three explicit constructor
Print cases). No snapshot preparation or proof-audit command runs here.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


prior = load('multiply_main_comparison', ARCHIVE.parent / 'scalar-add-integration/plan-main.py')
normal = load('multiply_ordered_records', ARCHIVE / 'review-normal.py')
# The imported comparator is private to this process. Its old record parser
# does not understand Print of constructors; every other comparison stays exact.
prior.contract_records = normal.contract_records
contract_records = normal.contract_records
compare_contracts = prior.compare_contracts


def plan(candidate):
    candidate = candidate.resolve()
    result = prior.plan(candidate)
    # The inherited planner only knows the scalar-add receipt. Do not let
    # that receipt, or a still-running multiply audit, imply acceptance here.
    del result['candidate_full_acceptance_receipt_present']
    result['candidate_full_acceptance'] = 'not asserted by this read-only planner'
    result['constructor_parent_print_aliases'] = [list(key) + [value]
                                                for key, value in normal.CONSTRUCTOR_PRINTS.items()]
    scripts = {}
    for name in ['check-jets.sh', 'jet-coverage.py', 'test-jet-coverage.py',
                 'audit-jet-contracts.sh']:
        main_data = (REPO / 'Coq' / name).read_bytes()
        candidate_data = (candidate / name).read_bytes()
        scripts[name] = {'identical': main_data == candidate_data,
                         'main_sha256': hashlib.sha256(main_data).hexdigest(),
                         'candidate_sha256': hashlib.sha256(candidate_data).hexdigest()}
    result['gate_scripts_to_review'] = scripts
    result['next'] = ('First obtain terminal full multiply acceptance and verify its frozen fingerprint. '
                      'Then resolve all source/inventory/snapshot/gate differences against the current '
                      'index and worktree, preserve main-only work, and fully verify main separately.')
    return result


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--candidate-coq', type=Path, required=True)
    cli.add_argument('--summary', action='store_true')
    args = cli.parse_args()
    result = plan(args.candidate_coq)
    if args.summary:
        result = {**{key: value for key, value in result.items()
                     if key not in {'new_source_files', 'inventory_extensions', 'index_metadata_sha256'}},
                  'new_source_count': len(result['new_source_files']),
                  'inventories': {name: {key: value for key, value in entry.items()
                                        if key not in {'candidate_additions', 'main_sha256', 'candidate_sha256'}}
                                  | {'candidate_addition_count': len(entry['candidate_additions'])}
                                  for name, entry in result['inventory_extensions'].items()}}
    print(json.dumps(result, indent=2))
