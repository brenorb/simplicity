"""Exact scalar-multiply public target/literal wiring; not execution acceptance."""
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


def check(repo, coq):
    inherited = load('multiply_recursive_ports', coq / 'scalar-integration-review/check-negate-ports.py')
    receipt = inherited.check(repo, coq / 'C', coq / 'C', coq)
    parser = load('multiply_active_parser', coq / 'check-secp-predicates-specification.py')
    catalog = parser.read_code(repo / 'Haskell/Core/Simplicity/CoreJets.hs')
    parser.require(catalog,
        'ScalarMultiply :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar',
        'scalar-multiply catalog type')
    parser.require(catalog, 'specificationSecp256k1 ScalarMultiply = Secp256k1.scalar_multiply',
        'scalar-multiply canonical dispatch')
    target = coq / 'C/jet_secp_scalar_multiply_local.v'
    code = parser.read_code(target)
    statements = re.findall(r'\bTheorem\s+scalar_multiply_literal_local_spec\s*:(.*?)\bProof\s*\.', code, re.S)
    wanted = ('secp_jet_local_spec f_simplicity_scalar_multiply '
              '(Ty.Prod (Word 8) (Word 8)) (Word 8) (@canonical_scalar_multiply Alg.CoreFunSem).')
    if len(statements) != 1 or parser.compact(statements[0]) != parser.compact(wanted):
        raise ValueError('public root is not the exact C-to-literal-Simplicity contract')
    paths = [coq / 'C' / name for name in [
        'jet_secp_normalize_local.v', 'jets_secp.v', 'jet_secp_linkage.v',
        'jet_secp_scalar_multiply_body.v', 'jet_secp_scalar_multiply_entry.v',
        'jet_secp_scalar_multiply_prepare.v', 'jet_secp_scalar_multiply_rest.v',
        'jet_secp_scalar_multiply_lifecycle.v', 'jet_secp_scalar_multiply_local.v']]
    receipt.update({'complete_public_C_contract': True,
                    'scalar_multiply_literal_dispatch': True,
                    'scope': 'local-frame / LP64 / RECKLESS; not assertion-enabled or all-jet completion',
                    'public_coverage_added': 0})
    receipt['hashes'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    return receipt


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--repo', type=Path, required=True)
    cli.add_argument('--coq', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(check(args.repo, args.coq), indent=2))
