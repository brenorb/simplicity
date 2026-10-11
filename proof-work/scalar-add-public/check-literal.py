"""Exact scalar-add public root and recursive literal program correspondence."""
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


def check(repo, source, coq):
    archive = Path(__file__).resolve().parent
    bridge = load('scalar_add_public_bridge', archive.parent / 'scalar-add-bridge/check-literal.py')
    receipt = bridge.check(repo, source, coq)
    parser = load('scalar_add_public_parser', coq / 'check-secp-predicates-specification.py')
    target = source / 'jet_secp_scalar_add_local.v'
    code = parser.read_code(target)
    statements = re.findall(r'\bTheorem\s+scalar_add_literal_local_spec\s*:(.*?)\bProof\s*\.', code, re.S)
    wanted = ('secp_jet_local_spec f_simplicity_scalar_add '
              '(Ty.Prod (Word 8) (Word 8)) (Word 8) (@canonical_scalar_add Alg.CoreFunSem).')
    if len(statements) != 1 or parser.compact(statements[0]) != parser.compact(wanted):
        raise ValueError('public root is not exact C-to-literal-Simplicity contract')
    # Freeze the inherited transparent contract, original program and actual
    # allocation/body/return/free adapters. Coq proves execution, not this gate.
    paths = [coq / 'C/jet_secp_normalize_local.v', coq / 'C/jets_secp.v',
             coq / 'C/jet_secp_linkage.v', coq / 'C/jet_secp_scalar_public_entry.v',
             coq / 'C/jet_secp_scalar_public_setup.v', coq / 'C/jet_secp_scalar_normalize_rest.v']
    paths += [source / name for name in [
        'jet_secp_scalar_writer_word.v', 'jet_secp_scalar_add_call_chain.v',
        'jet_secp_scalar_add_body.v', 'jet_secp_scalar_add_entry.v',
        'jet_secp_scalar_add_prepare.v', 'jet_secp_scalar_add_rest.v',
        'jet_secp_scalar_add_lifecycle.v', 'jet_secp_scalar_add_local.v']]
    receipt['complete_public_C_contract'] = True
    receipt['scope'] = 'local-frame / LP64 / RECKLESS, not evaluator or assertion-enabled'
    receipt['hashes'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths})
    return receipt


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    for name in ['repo', 'source', 'coq']:
        cli.add_argument('--' + name, type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(check(args.repo, args.source, args.coq), indent=2))
