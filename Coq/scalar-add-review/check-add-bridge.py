"""Scoped scalar-add literal wiring; supplements Coq, not public acceptance."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, source, coq):
    archive = Path(__file__).resolve().parent
    # Recheck the literal modulo/group constant and recursive dependency ports.
    scalar = load('scalar_add_scalar_dependencies', coq / 'scalar-integration-review/check-negate-ports.py')
    inherited = scalar.check(repo, coq / 'C', coq / 'C', coq)
    # Carry expansion is identical for field and scalar addition. This gate
    # checks one/zero/padding/add against Haskell and the actual reused term.
    add = load('scalar_add_common_carry', coq / 'add-review/check-add-wiring.py')
    if add.check(add.load(repo, coq / 'C', coq / 'C')) != 10:
        raise ValueError('unexpected common carry port scope')
    recursive = load('scalar_add_active_parser', coq / 'negate-review/check-recursive-ports.py')
    parser = recursive.parser(repo)
    catalog = parser.read_code(repo / 'Haskell/Core/Simplicity/CoreJets.hs')
    parser.require(catalog,
        'ScalarAdd :: Secp256k1Jet (Secp256k1.Scalar, Secp256k1.Scalar) Secp256k1.Scalar',
        'scalar-add catalog type')
    parser.require(catalog, 'specificationSecp256k1 ScalarAdd = Secp256k1.scalar_add',
        'scalar-add dispatch')
    program = parser.read_code(repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs')
    parser.exact_program(program.split('lib@Lib{..} = Lib {', 1)[1], 'scalar_add', 'scalar_negate',
        'add256 >>> cond ((unit >>> one256) &&& iden) ((unit >>> zero256) &&& iden) >>> scalar_normalize512')
    port = source / 'jet_secp_canonical_scalar_add.v'
    expected = '''Definition canonical_scalar_add {term : Alg.Core.Algebra} :
      term (Ty.Prod (Word 8) (Word 8)) (Word 8) :=
      @canonical_add_word 8 term >>> @literal_fe_add_expand term
        >>> @canonical_scalar_normalize512 term.'''
    if parser.compact(recursive.declaration(parser.read_code(port), 'canonical_scalar_add')) != parser.compact(expected):
        raise ValueError('scalar-add typed literal port differs')
    paths = [port, coq / 'C/jet_secp_literal_add_program.v',
             coq / 'C/jet_secp_canonical_scalar_negate.v',
             coq / 'add-review/check-add-wiring.py',
             repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
             repo / 'Haskell/Core/Simplicity/Programs/Word.hs', repo / 'Coq/C/jet_spec.v']
    return {'literal_scalar_add_structure': True, 'recursive_dependency_gate': True,
            'common_carry_padding_gate': True, 'complete_public_C_contract': False,
            'public_coverage_added': 0,
            'hashes': {**inherited['hashes'],
                       **{str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}}}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    for name in ['repo', 'source', 'coq']:
        cli.add_argument('--' + name, type=Path, required=True)
    a = cli.parse_args()
    print(json.dumps(check(a.repo, a.source, a.coq), indent=2))
