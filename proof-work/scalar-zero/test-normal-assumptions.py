"""In-memory reconciliation failures; never change a frozen audit input."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch
sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('normal_assumptions', archive / 'review-normal-assumptions.py')
reviewer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reviewer)
receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
candidate = Path(receipt['candidate']) / 'Coq'


def reject(path, transform):
    original_bytes, original_text = Path.read_bytes, Path.read_text
    baseline = original_bytes(path)
    changed = transform(baseline)
    if changed == baseline:
        raise AssertionError('fixture did not mutate input')
    def read_bytes(p, *args, **kwargs):
        return changed if p == path else original_bytes(p, *args, **kwargs)
    def read_text(p, *args, **kwargs):
        return changed.decode() if p == path else original_text(p, *args, **kwargs)
    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            reviewer.review()
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + str(path))


if __name__ == '__main__':
    report = reviewer.review()
    if report['inherited_results_unchanged'] != 4055 or report['added_results'] != 178:
        raise AssertionError('unexpected scope')
    snapshot = candidate / 'C/jet_assumptions.expected'
    reject(candidate / 'C/jet_encoding.v', lambda b: b + b'\n(* inherited source drift *)\n')
    reject(candidate / 'C/jet_secp_scalar_zero_local.v', lambda b: b + b'\n(* added source drift *)\n')
    reject(candidate / 'C/jet_contract_definitions.txt', lambda b: b + b'C.unknown bogus\n')
    reject(snapshot, lambda b: b.replace(b' : closed', b' : Untrusted.new_axiom', 1))
    reject(snapshot, lambda b: b.replace(b'C.jet_secp_scalar_zero_local.scalar_zero_local_spec : ',
                                       b'C.jet_secp_scalar_zero_local.scalar_zero_local_spec : Untrusted.new_axiom, ', 1))
    reject(snapshot, lambda b: b + b.splitlines()[0] + b'\n')
    reject(snapshot, lambda b: b.replace(b'C.jet_secp_scalar_zero_local.scalar_zero_local_spec : ',
                                       b'C.jet_secp_scalar_zero_local.wrong_result : ', 1))
    reject(Path(receipt['work']) / 'assumptions-review.out', lambda b: b + b'\nchanged historical report\n')
    reviewer.review()
    print('4055 inherited and 178 added dependency records match; eight in-memory mutations rejected')
