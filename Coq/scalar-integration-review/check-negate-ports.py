"""Scoped literal scalar-negate wiring and literal division substitution; not C acceptance."""
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


def check(repo, source, dependencies, coq):
    archive = Path(__file__).resolve().parent
    scalar = load('scalar_ports', coq / 'scalar-review/check-scalar-ports.py')
    if scalar.check(repo, dependencies, coq) != 2:
        raise ValueError('unexpected base scalar scope')
    recursive = load('source_helpers', coq / 'source-review.py')
    parser = recursive.parser(repo)
    literal = load('literal_ports', coq / 'negate-review/check-literal-ports.py')
    h, p, ports = literal.load(repo, coq / 'C', coq / 'negate-review')
    if literal.check(h, p, ports) != 14:
        raise ValueError('unexpected recursive literal-add scope')
    program = parser.read_code(repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs')
    catalog = parser.read_code(repo / 'Haskell/Core/Simplicity/CoreJets.hs')
    parser.require(catalog, 'ScalarNegate :: Secp256k1Jet Secp256k1.Scalar Secp256k1.Scalar', 'scalar-negate type')
    parser.require(catalog, 'specificationSecp256k1 ScalarNegate = Secp256k1.scalar_negate', 'scalar-negate dispatch')
    impl = program.split('lib@Lib{..} = Lib {', 1)[1]
    parser.exact_program(impl, 'scalar_negate', 'scalar_square',
        '(unit >>> scribe256 ((-1) `mod` LibSecp256k1.groupOrder)) &&& iden >>> scalar_multiply')
    parser.exact_program(impl, 'scalar_multiply', 'scalar_multiply_lambda', 'mul256 >>> scalar_normalize512')
    for wanted in [
        'scribe256 = scribe . toWord256', 'scribeGroupOrder = scribe256 LibSecp256k1.groupOrder',
        'mul256 = Arith.multiply word256', 'zero256 = Arith.zero word256', 'mod512 = Arith.modulo word512',
        'scalar_normalize512 = iden &&& (unit >>> zero256 &&& scribeGroupOrder) >>> mod512 >>> ih',
    ]:
        parser.require(program, wanted, 'scalar helper binding')
    port = parser.read_code(source / 'jet_secp_canonical_scalar_negate.v')
    bodies = {
        'canonical_scalar_normalize512': 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_group_word)) >>> @literal_modulo_word_spec 9 term >>> I H',
        'canonical_scalar_multiply': '@multiply_word_spec 8 term >>> @canonical_scalar_normalize512 term',
        'canonical_scalar_negate_factor': '@fromZ (WordToZ 8) ((-1) mod canonical_group_order)',
        'canonical_scalar_negate': '(unit >>> Alg.scribe canonical_scalar_negate_factor) &&& iden >>> @canonical_scalar_multiply term',
    }
    for name, expected in bodies.items():
        recursive.declaration(port, name)  # Exactly one active declaration.
        if parser.compact(parser.definition(port, name)) != parser.compact(expected):
            raise ValueError('scalar literal port differs: ' + name)
    paths = [repo / f for f in scalar.files] + [dependencies / f for f in scalar.ports]
    paths += [coq / 'C' / f for f in ['jet_literal_division_add.v', 'jet_canonical_add_adapter.v', 'jet_secp_negate_literal_contract.v']]
    paths += [source / 'jet_secp_canonical_scalar_negate.v']
    return {'literal_scalar_ports': 6, 'scalar_negate_literal_structure': True,
            'literal_division_gate': True, 'complete_literal_public_contract': False,
            'public_coverage_added': 0,
            'hashes': {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    for name in ['repo', 'source', 'dependencies', 'coq']:
        cli.add_argument('--' + name, type=Path, required=True)
    a = cli.parse_args()
    print(json.dumps(check(a.repo, a.source, a.dependencies, a.coq), indent=2))
