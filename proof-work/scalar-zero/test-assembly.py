"""Reject assembly drift in memory; never mutate an active build's inputs."""
from pathlib import Path
import importlib.util
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('scalar_assembly', archive / 'assemble-candidate.py')
assembler = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assembler)


def reject(base, work, candidate, target, transform):
    original_bytes, original_text = Path.read_bytes, Path.read_text
    altered = transform(original_bytes(target))

    def read_bytes(path, *args, **kwargs):
        return altered if path == target else original_bytes(path, *args, **kwargs)

    def read_text(path, *args, **kwargs):
        return altered.decode() if path == target else original_text(path, *args, **kwargs)

    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            assembler.assemble(base, work, candidate, verify=True)
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + str(target))


if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('usage: test-assembly.py BASELINE SCRATCH CANDIDATE')
    base, work, candidate = [Path(p).resolve() for p in sys.argv[1:]]
    result = assembler.assemble(base, work, candidate, verify=True)
    mutations = [
        (base / 'Coq/C/jet_secp_normalize_local.v', lambda b: b + b'\n(* baseline drift *)\n'),
        (work / 'jet_secp_scalar_zero_local.v', lambda b: b + b'\n(* scratch drift *)\n'),
        (candidate / 'Coq/C/jet_secp_scalar_zero_local.v', lambda b: b + b'\n(* candidate drift *)\n'),
        (candidate / 'Coq/C/jet_secp_local_regions.v', lambda b: b + b'\n(* inherited module drift *)\n'),
        (candidate / 'Coq/_CoqProject.jets', lambda b: b + b'C/unregistered.v\n'),
        (candidate / 'Coq/C/jet_contracts.expected', lambda b: b + b'\nunchecked snapshot\n'),
        (candidate / 'Coq/jet-coverage.py', lambda b: b.replace(b'"simplicity_scalar_is_zero"', b'"simplicity_scalar_normalize"', 1)),
        (candidate / 'Coq/scalar-review/check-literal.py', lambda b: b + b'\n# source gate drift\n'),
    ]
    for target, transform in mutations:
        reject(base, work, candidate, target, transform)
    assembler.assemble(base, work, candidate, verify=True)
    print('assembly baseline passed; eight in-memory source/metadata/snapshot/gate mutations rejected')
