"""Check the installed direct-getter delta and historical/current terminal receipts."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('direct_installed_gate', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def check():
    support = gate.support
    ledger = json.loads((HERE / 'INSTALLATION.json').read_text())
    work = Path(ledger['candidate'])
    accepted = json.loads((work / 'ACCEPTANCE.json').read_text())
    sequence_path = HERE.parent / 'elements-sequence-admission/MAIN-ACCEPTANCE.json'
    sequence = json.loads(sequence_path.read_text())
    marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
    def terminal(receipt, scope, expected_input):
        log = Path(receipt['log'])
        if (receipt['exit_code'] != 0 or receipt[scope] is not True or
                receipt['command'] != ['bash', 'check-jets.sh', '--accept'] or
                receipt['audit_input_sha256'] != expected_input or
                support.sha(log.read_bytes()) != receipt['log_sha256'] or
                not log.read_text().rstrip().endswith(marker)):
            raise ValueError('terminal acceptance scope/input/log evidence changed')
    if (ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
            ledger['coverage'] != '371/533' or ledger['coverage_added'] != 3 or
            ledger['prior_sequence_main_acceptance_sha256'] != support.sha(sequence_path.read_bytes()) or
            ledger['isolated_acceptance_sha256'] != support.sha((work / 'ACCEPTANCE.json').read_bytes())):
        raise ValueError('installation/prerequisite receipt scope changed')
    terminal(sequence, 'actual_main_acceptance', ledger['before_input_sha256'])
    terminal(accepted, 'full_acceptance', ledger['candidate_input_sha256'])
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    expected = dict(meta['main_inputs'])
    expected.update(ledger['installed_sha256'])
    if expected != support.input_map() or support.index_hash() != ledger['main_staged_patch_sha256']:
        raise ValueError('main source/index differs from exact reviewed installation')
    for name, digest in ledger['installed_sha256'].items():
        if support.sha((gate.REPO / name).read_bytes()) != digest:
            raise ValueError('installed source/metadata/gate drift')
    fingerprint = support.inputs.fingerprint(gate.MAIN, gate.REPO)
    if fingerprint != ledger['candidate_input_sha256'] or fingerprint != support.inputs.fingerprint(work / 'Coq', work):
        raise ValueError('main/accepted candidate input identity changed')
    actual_main = False
    path = HERE / 'MAIN-ACCEPTANCE.json'
    if path.exists():
        receipt = json.loads(path.read_text())
        terminal(receipt, 'actual_main_acceptance', fingerprint)
        actual_main = True
    result = {'coverage': '371/533', 'staged_patch_preserved': True,
              'prior_sequence_main_acceptance_verified': True,
              'source_identical_to_accepted_candidate': True, 'actual_main_acceptance': actual_main}
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
