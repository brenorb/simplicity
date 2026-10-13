"""Read-only cumulative main reconciliation; optional fresh report only.

No source/index installation or acceptance is performed. The separately
recorded report may be saved through apply_patch outside all audited inputs.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
from pathlib import PurePosixPath
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent
SCOPED = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
          'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv', 'C/jet_assumptions.expected',
          'C/jet_contracts.expected', 'C/jet_coqchk_axioms.expected', 'check-jets.sh',
          'jet-coverage.py', 'test-jet-coverage.py', 'audit-jet-contracts.sh']


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


prior = load('square_main_prior', ARCHIVE.parent / 'scalar-multiply-integration/plan-main.py')
sha = lambda data: hashlib.sha256(data).hexdigest()


def main_state():
    state = {}
    for name in SCOPED:
        result = subprocess.run(['git', 'show', ':Coq/' + name], cwd=REPO,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        state[name] = {'index_sha256': sha(result.stdout),
                       'worktree_sha256': sha((REPO / 'Coq' / name).read_bytes())}
    staged = subprocess.run(['git', 'diff', '--cached', '--binary'], cwd=REPO,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return {'scoped': state, 'whole_staged_patch_sha256': sha(staged.stdout)}


def assets(candidate):
    added, same, conflicts = [], [], []
    for path in sorted(candidate.rglob('*')):
        if not path.is_file() or '__pycache__' in path.parts:
            continue
        if path.suffix not in {'.py', '.sh', '.json', '.source', '.c', '.in', '.ini'}:
            continue
        rel = str(path.relative_to(candidate)); target = REPO / 'Coq' / rel
        raw = path.read_bytes()
        if not target.exists():
            added.append({'path': rel, 'sha256': sha(raw)})
        elif target.read_bytes() == raw:
            same.append(rel)
        else:
            conflicts.append({'path': rel, 'main_sha256': sha(target.read_bytes()),
                              'candidate_sha256': sha(raw),
                              'explicit_gate_review': rel in SCOPED})
    return {'new_gate_and_provenance_assets': added, 'identical_existing_assets': same,
            'asset_conflicts_to_review': conflicts}


def plan(candidate):
    candidate = candidate.resolve(); before = main_state()
    result = prior.plan(candidate)
    result.update(assets(candidate))
    after = main_state()
    if before != after:
        raise ValueError('main index/worktree metadata changed during read-only planning')
    result['main_state'] = after
    result['candidate_full_acceptance'] = 'not asserted by this read-only planner; square audit may still be running'
    result['next'] = ('Require terminal full square acceptance with its frozen fingerprint. '
                      'Recompute this plan and all scoped hashes before applying; preserve index contents, '
                      'existing worktree rows/bytes and main-only sources. Review every gate/asset conflict '
                      'explicitly and fully verify main separately. No report authorizes overwriting later changes.')
    return result


def summary(result):
    omit = {'new_source_files', 'inventory_extensions', 'index_metadata_sha256',
            'new_gate_and_provenance_assets', 'identical_existing_assets'}
    return {**{key: value for key, value in result.items() if key not in omit},
            'new_source_count': len(result['new_source_files']),
            'new_asset_count': len(result['new_gate_and_provenance_assets']),
            'identical_asset_count': len(result['identical_existing_assets']),
            'inventories': {name: {key: value for key, value in entry.items()
                                  if key not in {'candidate_additions', 'main_sha256', 'candidate_sha256'}}
                            | {'candidate_addition_count': len(entry['candidate_additions'])}
                            for name, entry in result['inventory_extensions'].items()}}


def validate_preserving_plan(result):
    """Reject unsafe reconciliation proposals; this does not prove acceptance."""
    if (result['source_conflicts'] or result['changed_existing_dependencies']
            or not result['inherited_contract_bytes_identical']
            or not result['inherited_contract_order_preserved']
            or result['changed_contract_records'] or result['missing_contract_records']
            or not result['kernel_allowlist_identical']):
        raise ValueError('proposal changes existing sources/contracts/dependencies')
    for entry in result['inventory_extensions'].values():
        if (not entry['main_rows_preserved_in_order'] or entry['main_rows_missing']
                or not entry['main_is_byte_prefix']):
            raise ValueError('proposal discards or reorders worktree inventory')
    approved = {'check-jets.sh', 'jet-coverage.py', 'test-jet-coverage.py', 'audit-jet-contracts.sh'}
    conflicts = result['asset_conflicts_to_review']
    if {entry['path'] for entry in conflicts} != approved or any(not entry['explicit_gate_review'] for entry in conflicts):
        raise ValueError('new/unreviewed asset conflict')
    for entry in result['new_source_files'] + result['new_gate_and_provenance_assets']:
        path = PurePosixPath(entry['path'])
        if path.is_absolute() or '..' in path.parts or str(path) != entry['path']:
            raise ValueError('nonlocal/ambiguous proposed path')
    if result['writes_performed'] or result['checkout_coverage_added'] != 0:
        raise ValueError('read-only proposal claims installation/coverage')


def save_fresh_report(path, result):
    path = path.resolve()
    if (not str(path).startswith('/private/tmp/') or path.exists()
            or not path.parent.is_dir() or not path.parent.name.startswith('jet-square-main-plan.')
            or path.suffix != '.json'
            or 'Coq' in path.parts):
        raise ValueError('report must be a fresh JSON in a dedicated temporary directory, outside audit inputs')
    content = json.dumps(result, indent=2)
    patch = '*** Begin Patch\n*** Add File: ' + str(path) + '\n'
    patch += '\n'.join('+' + line for line in content.splitlines()) + '\n*** End Patch\n'
    subprocess.run(['apply_patch'], input=patch, text=True, check=True, stdout=subprocess.DEVNULL)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate-coq', type=Path, required=True)
    cli.add_argument('--summary', action='store_true'); cli.add_argument('--report', type=Path)
    args = cli.parse_args(); result = plan(args.candidate_coq)
    if args.report:
        save_fresh_report(args.report, result)
    print(json.dumps(summary(result) if args.summary else result, indent=2))
