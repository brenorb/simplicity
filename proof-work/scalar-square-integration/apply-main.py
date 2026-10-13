"""Apply the exact reviewed cumulative addition to main's worktree only.

Requires terminal square acceptance, a still-identical preservation plan,
and explicit --apply. Never stages, commits, copies objects or updates proofs.
"""
import argparse
import difflib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent
spec = importlib.util.spec_from_file_location('square_main_plan', ARCHIVE / 'plan-main.py')
planner = importlib.util.module_from_spec(spec); spec.loader.exec_module(planner)


def acceptance(candidate):
    receipt = json.loads((ARCHIVE / 'ACCEPTANCE.json').read_text())
    if (receipt['exit_code'] != 0 or not receipt['post_run_snapshot_review_passed']
            or (Path(receipt['candidate']).resolve() / 'Coq') != candidate):
        raise ValueError('candidate lacks matching terminal acceptance')
    log = Path(receipt['log']).read_bytes()
    if planner.sha(log) != receipt['log_sha256'] or b'all jet acceptance checks passed' not in log:
        raise ValueError('terminal acceptance log changed/incomplete')
    audit = planner.load('square_apply_inputs', candidate / 'jet-audit-inputs.py')
    if audit.fingerprint(candidate, REPO) != receipt['audit_input_sha256']:
        raise ValueError('accepted candidate input fingerprint changed')
    normal = planner.load('square_apply_normal', ARCHIVE / 'review-normal.py')
    normal.review(ARCHIVE / 'ASSEMBLY.json')
    return receipt


def apply(plan_path, write=False):
    recorded = json.loads(plan_path.read_text()); candidate = Path(recorded['candidate']).resolve()
    acceptance(candidate)
    current = planner.plan(candidate)
    if current != recorded:
        raise ValueError('main/candidate/index changed since recorded plan; recompute and review')
    planner.validate_preserving_plan(current)
    main = REPO / 'Coq'; additions, replacements, originals = {}, {}, {}
    for entry in current['new_source_files'] + current['new_gate_and_provenance_assets']:
        name = entry['path']; path = candidate / name
        if planner.sha(path.read_bytes()) != entry['sha256'] or (main / name).exists():
            raise ValueError('new-file provenance/target changed: ' + name)
        additions[name] = path.read_text()
    names = list(current['inventory_extensions']) + ['C/jet_assumptions.expected', 'C/jet_contracts.expected']
    names += [entry['path'] for entry in current['asset_conflicts_to_review']]
    for name in names:
        originals[name] = (main / name).read_text(); replacements[name] = (candidate / name).read_text()
    # Preserve every existing source and main-only file, not just metadata.
    protected = {str(path.relative_to(main)): planner.sha(path.read_bytes()) for path in main.rglob('*.v')}
    staged_before = current['main_state']['whole_staged_patch_sha256']
    patch = ['*** Begin Patch']
    for name, content in additions.items():
        patch += ['*** Add File: ' + str(main / name)] + ['+' + line for line in content.splitlines()]
    for name, content in replacements.items():
        patch.append('*** Update File: ' + str(main / name))
        diff = list(difflib.unified_diff(originals[name].splitlines(), content.splitlines(), n=3))[2:]
        patch += ['@@' if line.startswith('@@') else line for line in diff]
    patch.append('*** End Patch')
    if write:
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
        for name, content in {**additions, **replacements}.items():
            if (main / name).read_bytes() != content.encode():
                raise ValueError('installed source/metadata differs: ' + name)
        for name, value in protected.items():
            if planner.sha((main / name).read_bytes()) != value:
                raise ValueError('preexisting source changed: ' + name)
        after = planner.main_state()
        if (after['whole_staged_patch_sha256'] != staged_before
                or any(after['scoped'][name]['index_sha256'] != row['index_sha256']
                       for name, row in current['main_state']['scoped'].items())):
            raise ValueError('preexisting staging changed')
    return {'candidate': str(candidate), 'main': str(main), 'applied_worktree_only': write,
            'new_sources': len(current['new_source_files']),
            'new_gate_assets': len(current['new_gate_and_provenance_assets']),
            'updated_metadata_and_gates': sorted(replacements),
            'protected_existing_sources': len(protected), 'index_unchanged': True,
            'preexisting_staged_patch_sha256': staged_before,
            'main_full_acceptance': False,
            'next': 'Verify the actual main tree fully; do not stage or commit unrelated existing changes.'}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--plan', type=Path, required=True)
    cli.add_argument('--apply', action='store_true'); args = cli.parse_args()
    print(json.dumps(apply(args.plan, args.apply), indent=2))
