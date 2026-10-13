"""Read-only lambda integration plan; no source/index/acceptance writes."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


prior = load('lambda_preserving_core', ARCHIVE.parent / 'scalar-square-integration/plan-main.py')
sha, main_state = prior.sha, prior.main_state
summary = prior.summary


def plan(candidate):
    candidate = candidate.resolve()
    result = prior.plan(candidate)
    inputs = load('lambda_integration_inputs', candidate / 'jet-audit-inputs.py')
    main_receipt = json.loads((ARCHIVE.parent / 'scalar-square-integration/MAIN-ACCEPTANCE.json').read_text())
    current_main = inputs.fingerprint(REPO / 'Coq', REPO)
    result['main_accepted_input_sha256'] = main_receipt['audit_input_sha256']
    result['current_main_input_sha256'] = current_main
    result['main_acceptance_current'] = (
        main_receipt['exit_code'] == 0
        and main_receipt['full_main_acceptance']
        and current_main == main_receipt['audit_input_sha256']
        and sha(Path(main_receipt['log']).read_bytes()) == main_receipt['log_sha256'])
    result['candidate_input_sha256'] = inputs.fingerprint(candidate, REPO)
    result['candidate_full_acceptance'] = 'not asserted by this read-only planner; lambda audit is separate'
    result['next'] = ('Require terminal lambda acceptance and unchanged fingerprint/post-run review. '
                      'Recompute this preserving plan before applying; do not overwrite later changes, '
                      'stage unrelated work, or infer actual-main acceptance from isolated acceptance.')
    return result


def validate_preserving_plan(result):
    prior.validate_preserving_plan(result)
    assembly = json.loads((ARCHIVE / 'ASSEMBLY.json').read_text())
    preparation = json.loads((ARCHIVE / 'PREPARATION.json').read_text())
    if ((Path(assembly['candidate']).resolve() / 'Coq') != Path(result['candidate']).resolve()
            or result['candidate_input_sha256'] != preparation['frozen_preacceptance_fingerprint']
            or not result['main_acceptance_current']
            or result['current_main_input_sha256'] != result['main_accepted_input_sha256']):
        raise ValueError('current main/candidate does not match reviewed input boundary')
    sources = {e['path']: e['sha256'] for e in result['new_source_files']}
    assets = {e['path']: e['sha256'] for e in result['new_gate_and_provenance_assets']}
    wanted_sources = {p: h for p, h in assembly['added_file_hashes'].items() if p.endswith('.v')}
    wanted_assets = {p: h for p, h in assembly['added_file_hashes'].items() if not p.endswith('.v')}
    if (len(result['new_source_files']) != 28 or sources != wanted_sources
            or len(result['new_gate_and_provenance_assets']) != 2 or assets != wanted_assets):
        raise ValueError('proposal is not exactly the reviewed lambda source/gate addition')
    rows = {
        '_CoqProject': ['C/' + e['name'] + '.v' for e in assembly['modules']],
        '_CoqProject.jets': ['C/' + e['name'] + '.v' for e in assembly['modules']],
        'C/jet_public_theorems.txt': ['C.' + e['name'] + ' ' + n
                                    for e in assembly['modules'] for n in e['results']],
        'C/jet_contract_definitions.txt': ['C.' + e['name'] + ' ' + n
                                          for e in assembly['modules'] for n in e['definitions']],
        'C/jet_coverage.tsv': ['simplicity_scalar_multiply_lambda\tC.jet_secp_scalar_lambda_local\tscalar_lambda_initialized_local_spec'],
    }
    if (set(result['inventory_extensions']) != set(rows)
            or any(result['inventory_extensions'][name]['candidate_additions'] != wanted
                   for name, wanted in rows.items())
            or result['candidate_assumption_records'] - result['inherited_assumption_records'] != 116
            or result['new_contract_records'] != 148):
        raise ValueError('proposal has an unreviewed inventory/snapshot extension')


def save_fresh_report(path, result):
    path = path.resolve()
    if (not str(path).startswith('/private/tmp/') or path.exists()
            or not path.parent.is_dir() or not path.parent.name.startswith('jet-lambda-main-plan.')
            or path.suffix != '.json' or 'Coq' in path.parts):
        raise ValueError('report must be fresh JSON in a dedicated temporary directory outside audited inputs')
    patch = '*** Begin Patch\n*** Add File: ' + str(path) + '\n'
    patch += '\n'.join('+' + line for line in json.dumps(result, indent=2).splitlines()) + '\n*** End Patch\n'
    subprocess.run(['apply_patch'], input=patch, text=True, check=True, stdout=subprocess.DEVNULL)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate-coq', type=Path, required=True)
    cli.add_argument('--summary', action='store_true'); cli.add_argument('--report', type=Path)
    args = cli.parse_args(); result = plan(args.candidate_coq); validate_preserving_plan(result)
    if args.report:
        save_fresh_report(args.report, result)
    print(json.dumps(summary(result) if args.summary else result, indent=2))

