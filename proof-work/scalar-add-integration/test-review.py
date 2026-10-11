"""Reject source/type/dependency/evidence drift without writing audit inputs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('normal_scalar_add_review', archive / 'review-normal.py')
reviewer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(reviewer)


def reject(target, transform):
    original_bytes, original_text = Path.read_bytes, Path.read_text
    altered = transform(original_bytes(target))
    if altered == original_bytes(target):
        raise AssertionError('fixture did not alter its target: ' + str(target))

    def read_bytes(path, *args, **kwargs):
        return altered if path == target else original_bytes(path, *args, **kwargs)

    def read_text(path, *args, **kwargs):
        return altered.decode() if path == target else original_text(path, *args, **kwargs)

    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            reviewer.review(preliminary=True)
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + str(target))


if __name__ == '__main__':
    receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
    work = Path(receipt['candidate'])
    candidate = work / 'Coq'
    reviewer.review(preliminary=True)
    tests = [
        (candidate / 'C/jet_secp_scalar_add_local.v',
         lambda b: b.replace(b'canonical_scalar_add', b'canonical_scalar_normalize', 1)),
        (candidate / 'C/jet_assumptions.expected',
         lambda b: b.replace(b'C.jet_secp_scalar_add_flag.scalar_add_flag_integer : closed',
                             b'C.jet_secp_scalar_add_flag.scalar_add_flag_integer : FunctionalExtensionality.functional_extensionality_dep', 1)),
        (work / 'new-assumptions.out',
         lambda b: b.replace(b'JET_ASSUMPTIONS C.jet_secp_scalar_add_local.scalar_add_literal_local_spec',
                             b'JET_ASSUMPTIONS C.jet_secp_scalar_add_local.missing_result', 1)),
        (candidate / 'C/jet_contracts.expected',
         lambda b: b.replace(b'secp_jet_local_spec jets_secp.f_simplicity_scalar_add',
                             b'secp_jet_local_spec jets_secp.f_simplicity_scalar_normalize', 1)),
        (work / 'deep-full-contracts.out',
         lambda b: b.replace(b'SCALAR_TYPE C.jet_secp_scalar_add_local.scalar_add_literal_local_spec',
                             b'SCALAR_TYPE C.jet_secp_scalar_add_local.missing_result', 1)),
        (candidate / 'C/jet_coqchk_axioms.expected', lambda b: b + b'new_oracle\n'),
        (candidate / 'C/jet_public_theorems.txt',
         lambda b: b.replace(b'C.jet_secp_scalar_add_local scalar_add_literal_local_spec\n', b'', 1)),
        (candidate / 'scalar-add-review/check-add-public.py', lambda b: b + b'\n# gate drift\n'),
    ]
    for target, transform in tests:
        reject(target, transform)
    reviewer.review(preliminary=True)
    print('normal scalar-add review passed; eight in-memory evidence/type/dependency mutations rejected')
