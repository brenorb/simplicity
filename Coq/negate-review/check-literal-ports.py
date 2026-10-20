"""Check the reviewed division ports with literal-add substitution and final contract.

No generation/update mode; this is source evidence supplementing kernel checks.
"""
import argparse
import importlib.machinery
import importlib.util
import re
from pathlib import Path

NAMES = ['div3n2n_approx_spec', 'div3n2n_loop2_spec', 'div3n2n_loop1_spec',
         'div3n2n_loop0_spec', 'div3n2n_body_spec', 'div3n2n_word_builder',
         'div2n1n_word_spec', 'div3n2n_word_spec', 'div_mod_word_spec', 'modulo_word_spec']


def helper(directory):
    path = Path(directory).parent/'source-review.py'
    loader = importlib.machinery.SourceFileLoader('recursive_ports', str(path))
    spec = importlib.util.spec_from_loader(loader.name, loader)
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


def load(repo, candidates, gate_directory):
    h = helper(gate_directory)
    p = h.parser(repo)
    paths = {'original': Path(repo)/'Coq/C/jet_division_core_spec.v',
             'division': Path(candidates)/'jet_literal_division_add.v',
             'add': Path(candidates)/'jet_canonical_add_adapter.v',
             'field': Path(candidates)/'jet_secp_negate_literal_contract.v'}
    return h, p, {k: h.active(p, path, path.read_text()) for k, path in paths.items()}


def check(h, p, sources):
    for name in NAMES:
        expected = h.declaration(sources['original'], name)
        for old in NAMES:
            expected = expected.replace(old, 'literal_'+old)
        expected = expected.replace('@Word.adder', '@canonical_add_word')
        actual = h.declaration(sources['division'], 'literal_'+name)
        if p.compact(actual) != p.compact(expected):
            raise ValueError('literal division substitution differs '+name)
    expected_add = '''Definition canonical_add_word n {term : Alg.Core.Algebra} :
      term (Ty.Prod (Word n) (Word n)) (Ty.Prod Bit (Word n)) :=
      Bit.false &&& iden >>> @Word.fullAdder n term.'''
    if p.compact(h.declaration(sources['add'], 'canonical_add_word')) != p.compact(expected_add):
        raise ValueError('literal canonical add differs')
    bodies = {
        'literal_fe_normalize512': 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @literal_modulo_word_spec 9 term >>> I H',
        'literal_fe_multiply': '@multiply_word_spec 8 term >>> @literal_fe_normalize512 term',
        'literal_fe_negate': 'Alg.scribe canonical_negate_factor &&& iden >>> @literal_fe_multiply term',
    }
    for name, expected in bodies.items():
        if p.compact(p.definition(sources['field'], name)) != p.compact(expected):
            raise ValueError('literal field program differs '+name)
    statement = re.search(r'Theorem fe_negate_literal_local_spec\s*:(.*?)\bProof\.', sources['field'], re.S)
    expected = 'secp_jet_local_spec f_simplicity_fe_negate (Word 8) (Word 8) (@literal_fe_negate Alg.CoreFunSem).'
    if not statement or p.compact(statement[1]) != p.compact(expected):
        raise ValueError('literal final public contract differs')
    return 14


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    p.add_argument('--gates', default=str(Path(__file__).parent))
    args = p.parse_args()
    h, parser, sources = load(args.repo, args.candidates, args.gates)
    print('Literal ports and final contract match:', check(h, parser, sources))
