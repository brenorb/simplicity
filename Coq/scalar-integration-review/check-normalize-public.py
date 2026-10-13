"""Check literal scalar ports and the complete public theorem's source type."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, source, dependencies, coq):
    archive = Path(__file__).resolve().parent
    scalar = load('scalar_ports', coq / 'scalar-review/check-scalar-ports.py')
    if scalar.check(repo, dependencies, coq) != 2:
        raise ValueError('unexpected scalar port scope')
    gate = load('canonical_gate', coq / 'check-secp-predicates-specification.py')
    local = gate.read_code(source / 'jet_secp_scalar_normalize_local.v')
    match = re.search(r'\bTheorem\s+scalar_normalize_local_spec\s*:(.*?)\bProof\s*\.', local, re.S)
    expected = ('secp_jet_local_spec f_simplicity_scalar_normalize (Word 8) (Word 8) '
                '(@canonical_scalar_normalize Alg.CoreFunSem).')
    if not match or gate.compact(match[1]) != gate.compact(expected):
        raise ValueError('public contract is not the literal scalar normalize term')
    if len(re.findall(r'\bTheorem\s+scalar_normalize_local_spec\b', local)) != 1:
        raise ValueError('duplicate public theorem')
    return {'literal_scalar_ports': 2, 'complete_literal_public_contract': True,
            'recursive_dependency_gate': True, 'public_coverage_added': 0,
            'hashes': {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in [repo / f for f in scalar.files]
                       + [dependencies / f for f in scalar.ports]
                       + [source / 'jet_secp_scalar_normalize_local.v']}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--dependencies', type=Path, required=True)
    parser.add_argument('--coq', type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.source, args.dependencies, args.coq), indent=2))
