"""Verify exact installed source identity and any completed main acceptance."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_installed_gate', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def check():
    ledger = json.loads((HERE / 'INSTALLATION.json').read_text())
    work = Path(ledger['candidate'])
    accepted = json.loads((work / 'ACCEPTANCE.json').read_text())
    if (ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
            ledger['isolated_acceptance_sha256'] != gate.support.sha((work / 'ACCEPTANCE.json').read_bytes()) or
            accepted['exit_code'] != 0 or accepted['full_acceptance'] is not True or
            accepted['command'] != ['bash', 'check-jets.sh', '--accept']):
        raise ValueError('invalid isolated acceptance/installation scope')
    if gate.support.sha((work / 'acceptance.log').read_bytes()) != accepted['log_sha256']:
        raise ValueError('isolated terminal log drift')
    marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
    if not (work / 'acceptance.log').read_text().rstrip().endswith(marker):
        raise ValueError('isolated acceptance incomplete')
    for name, digest in ledger['installed_sha256'].items():
        if gate.support.sha((gate.REPO / name).read_bytes()) != digest:
            raise ValueError('installed metadata/gate drift')
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    expected = dict(meta['main_inputs'])
    expected.update(ledger['installed_sha256'])
    if expected != gate.support.input_map():
        raise ValueError('unexpected main source change after installation')
    if gate.support.index_hash() != ledger['main_staged_patch_sha256']:
        raise ValueError('preexisting staging changed')
    fingerprint = gate.support.inputs.fingerprint(gate.MAIN, gate.REPO)
    if fingerprint != ledger['candidate_input_sha256'] or fingerprint != gate.support.inputs.fingerprint(work / 'Coq', work):
        raise ValueError('main/candidate source identity changed')
    actual_main = False
    path = HERE / 'MAIN-ACCEPTANCE.json'
    if path.exists():
        receipt = json.loads(path.read_text())
        log = Path(receipt['log'])
        if (receipt['exit_code'] != 0 or receipt['actual_main_acceptance'] is not True or
                receipt['command'] != ['bash', 'check-jets.sh', '--accept'] or
                receipt['audit_input_sha256'] != fingerprint or
                gate.support.sha(log.read_bytes()) != receipt['log_sha256'] or
                not log.read_text().rstrip().endswith(marker)):
            raise ValueError('main acceptance terminal/input evidence changed')
        actual_main = True
    result = {'coverage': '366/533', 'staged_patch_preserved': True,
              'source_identical_to_accepted_candidate': True, 'actual_main_acceptance': actual_main}
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
