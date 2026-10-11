"""Exact public scalar-negate theorem and pinned literal/recursive programs."""
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
    ports = load('scalar_negate_ports', archive.parent / 'scalar-negate-canonical/check-literal.py')
    receipt = ports.check(repo, source, dependencies, coq)
    if receipt['literal_scalar_ports'] != 6 or not receipt['recursive_dependency_gate']:
        raise ValueError('unexpected literal scope')
    parser = load('public_parser', coq / 'check-secp-predicates-specification.py')
    target = source / 'jet_secp_scalar_negate_local.v'
    code = parser.read_code(target)
    statements = re.findall(r'\bTheorem\s+scalar_negate_local_spec\s*:(.*?)\bProof\s*\.', code, re.S)
    wanted = ('secp_jet_local_spec f_simplicity_scalar_negate (Word 8) (Word 8) '
              '(@canonical_scalar_negate Alg.CoreFunSem).')
    if len(statements) != 1 or parser.compact(statements[0]) != parser.compact(wanted):
        raise ValueError('public contract is not the exact literal scalar-negate term')
    receipt['complete_literal_public_contract'] = True
    receipt['hashes'][str(target)] = hashlib.sha256(target.read_bytes()).hexdigest()
    contract = coq / 'C/jet_secp_normalize_local.v'
    receipt['hashes'][str(contract)] = hashlib.sha256(contract.read_bytes()).hexdigest()
    return receipt


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    for name in ['repo', 'source', 'dependencies', 'coq']:
        cli.add_argument('--' + name, type=Path, required=True)
    a = cli.parse_args()
    print(json.dumps(check(a.repo, a.source, a.dependencies, a.coq), indent=2))
