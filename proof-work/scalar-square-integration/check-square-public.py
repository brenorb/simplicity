"""Exact original C/public/literal square wiring; not proof acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
MODULES = ['jet_sx_rename', 'jet_secp_scalar_square512_run', 'jet_secp_scalar_square512_product',
           'jet_secp_square_product_reduce', 'jet_secp_scalar_square_body',
           'jet_secp_scalar_square_caller_alloc', 'jet_secp_scalar_square_caller_function',
           'jet_secp_scalar_square_caller_observed', 'jet_secp_canonical_scalar_square',
           'jet_secp_scalar_square_literal_owned', 'jet_secp_scalar_square_from_reader',
           'jet_secp_scalar_square_call_chain', 'jet_secp_scalar_square_rest',
           'jet_secp_scalar_square_lifecycle', 'jet_secp_scalar_square_local']


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def check(repo, coq):
    parent = load('square_parent_gate', coq / 'scalar-multiply-review/check-multiply-public.py')
    receipt = parent.check(repo, coq)
    parser = load('square_active_parser', coq / 'check-secp-predicates-specification.py')
    catalog = parser.read_code(repo / 'Haskell/Core/Simplicity/CoreJets.hs')
    parser.require(catalog, 'ScalarSquare :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar',
                   'scalar-square catalog type')
    parser.require(catalog, 'specificationSecp256k1 ScalarSquare = Secp256k1.scalar_square',
                   'scalar-square canonical dispatch')
    root = parser.read_code(coq / 'C/jet_secp_scalar_square_local.v')
    statements = re.findall(r'\bTheorem\s+scalar_square_literal_local_spec\s*:(.*?)\bProof\s*\.', root, re.S)
    want = 'secp_jet_local_spec f_simplicity_scalar_square (Word 8) (Word 8) (@canonical_scalar_square Alg.CoreFunSem).'
    if len(statements) != 1 or parser.compact(statements[0]) != parser.compact(want):
        raise ValueError('square public root function/types/target/premises changed')
    canonical = parser.read_code(coq / 'C/jet_secp_canonical_scalar_square.v')
    definitions = re.findall(r'\bDefinition\s+canonical_scalar_square\s*(.*?)\.\s*Lemma', canonical, re.S)
    want_def = '{term : Alg.Core.Algebra} : term (Word 8) (Word 8) := iden &&& iden >>> @canonical_scalar_multiply term'
    if len(definitions) != 1 or parser.compact(definitions[0]) != parser.compact(want_def):
        raise ValueError('literal canonical square term changed')
    haskell_path = repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    haskell = parser.read_code(haskell_path)
    parts = haskell.split('mkLib Sha256.Lib{..} = lib')
    if len(parts) != 2:
        raise ValueError('canonical mkLib boundary changed')
    fields = [line.strip() for line in parts[1].splitlines() if re.match(r'\s*, scalar_square\s*=', line)]
    if fields != [', scalar_square = iden &&& iden >>> scalar_multiply']:
        raise ValueError('canonical Haskell square field changed')
    paths = [coq / 'C' / (name + '.v') for name in MODULES] + [haskell_path]
    receipt['hashes'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths})
    receipt.update(complete_public_square_C_contract=True, scalar_square_literal_dispatch=True,
                   scope='local-frame / LP64 / RECKLESS; not main/evaluator/assertion-enabled/all-jet completion',
                   public_coverage_added=0)
    return receipt


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--repo', type=Path, required=True)
    cli.add_argument('--coq', type=Path, required=True); args = cli.parse_args()
    print(json.dumps(check(args.repo, args.coq), indent=2))
