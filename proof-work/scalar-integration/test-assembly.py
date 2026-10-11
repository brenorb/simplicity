"""Reject drift in memory without editing the parent or candidate."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('scalar_integration', archive / 'assemble-candidate.py')
assembler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assembler)


def reject(base, candidate, target, transform):
    original_bytes, original_text = Path.read_bytes, Path.read_text
    altered = transform(original_bytes(target))
    if altered == original_bytes(target):
        raise AssertionError('fixture did not alter its target')

    def read_bytes(path, *args, **kwargs):
        return altered if path == target else original_bytes(path, *args, **kwargs)

    def read_text(path, *args, **kwargs):
        return altered.decode() if path == target else original_text(path, *args, **kwargs)

    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            assembler.assemble(base, candidate, verify=True)
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + str(target))


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: test-assembly.py BASELINE CANDIDATE')
    base, candidate = [Path(p).resolve() for p in sys.argv[1:]]
    assembler.assemble(base, candidate, verify=True)
    mutations = [
        (base / 'Coq/C/jet_secp_normalize_local.v', lambda b: b + b'\n(* baseline drift *)\n'),
        (Path('/tmp/jet-scalar-negate.f4CRAT/jet_secp_scalar_negate_local.v'),
         lambda b: b.replace(b'canonical_scalar_negate', b'canonical_scalar_normalize', 1)),
        (candidate / 'Coq/C/jet_secp_scalar_get_b32_numeric.v',
         lambda b: b.replace(b'C.jet_secp_scalar_get_b32_exec', b'OriginalC.jet_secp_scalar_get_b32_exec', 1)),
        (candidate / 'Coq/C/jet_secp_local_regions.v', lambda b: b + b'\n(* inherited drift *)\n'),
        (candidate / 'Coq/_CoqProject.jets', lambda b: b + b'C/unregistered.v\n'),
        (candidate / 'Coq/C/jet_contracts.expected', lambda b: b + b'\nunchecked snapshot\n'),
        (candidate / 'Coq/jet-coverage.py',
         lambda b: b.replace(b'"simplicity_scalar_negate"', b'"simplicity_scalar_square"', 1)),
        (candidate / 'Coq/scalar-integration-review/check-negate-public.py',
         lambda b: b + b'\n# gate drift\n'),
    ]
    for target, transform in mutations:
        reject(base, candidate, target, transform)
    assembler.assemble(base, candidate, verify=True)
    print('exact 25-module closure verified; eight in-memory assembly mutations rejected')
