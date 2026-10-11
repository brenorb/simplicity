"""In-memory normal/deep contract mutations, including updated digest fixtures."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('normal_contract_review', archive / 'review-normal-contracts.py')
reviewer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reviewer)
receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
candidate = Path(receipt['candidate'])
pinned_path = archive / 'NORMAL-CONTRACT-REVIEW.json'


def reject(path, transform, digest_field=None):
    original_bytes, original_text = Path.read_bytes, Path.read_text
    altered = transform(original_bytes(path))
    pinned = json.loads(original_text(pinned_path))
    if digest_field:
        pinned[digest_field] = hashlib.sha256(altered).hexdigest()

    def read_bytes(p, *args, **kwargs):
        return altered if p == path else original_bytes(p, *args, **kwargs)

    def read_text(p, *args, **kwargs):
        if p == path:
            return altered.decode()
        if p == pinned_path and digest_field:
            return json.dumps(pinned)
        return original_text(p, *args, **kwargs)

    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            reviewer.review()
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + str(path))


if __name__ == '__main__':
    reviewer.review()
    normal = candidate / 'Coq/C/jet_contracts.expected'
    deep = candidate / 'scalar-deep-contracts.out'
    reject(candidate / 'scalar_deep_contracts.v', lambda b: b + b'\n(* drift *)\n')
    reject(candidate / 'scalar-deep-contracts.err', lambda b: b + b'Error: diagnostic\n')
    reject(deep, lambda b: b + b'\n...\n', 'deep_sha256')
    reject(deep, lambda b: b.replace(b'SCALAR_TYPE ', b'MISSING_TYPE ', 1), 'deep_sha256')
    reject(deep, lambda b: b + b'\nSCALAR_TYPE unexpected.marker\n', 'deep_sha256')
    reject(normal, lambda b: b.replace(b'frame_fields =', b'unknown_inherited_fields =', 1),
           'candidate_contract_snapshot_sha256')
    reject(normal, lambda b: b.replace(b'jet_secp_u128_shift64_expr.u128_field =', b'wrong_module.u128_field =', 1),
           'candidate_contract_snapshot_sha256')
    reject(candidate / 'Coq/C/jet_contract_definitions.txt', lambda b: b + b'C.unknown unexpected\n')
    reviewer.review()
    print('normal/deep contracts match; eight in-memory driver/diagnostic/inventory/identity mutations rejected')
