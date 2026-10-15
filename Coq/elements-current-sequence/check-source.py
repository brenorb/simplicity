"""Selected CurrentSequence source correspondence; not a proof checker.

Reuse the reviewed InputSequence port and check the extra CurrentIndex/assert
composition. No claim about any other current-input primitive is made.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, coq, sequence, literal):
    inherited = load('current_sequence_input_source', HERE.parent / 'elements-sequence-review/check-source.py')
    record = inherited.check(repo, coq, sequence)
    parser = load('current_sequence_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('current-sequence source differs: ' + label)

    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)

    def line(text, start, expected):
        matches = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous source clause: ' + start)
        equal(matches[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    parser.require(catalog, 'CurrentSequence :: TransactionJet () Word32', 'jet type')
    parser.require(catalog, 'import qualified Simplicity.Elements.Programs.Transaction.Lib as Prog', 'library import')
    line(catalog, 'specificationTransaction CurrentSequence', 'Prog.currentSequence')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    line(library, 'currentSequence', 'Transaction.currentSequence Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    parser.require(program, 'lib = l where l@Lib{..} = Lib {', 'selected library')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous library definition')
    matches = re.findall(r'(?m)^\s*, currentSequence\s*=([^\n]*)$', program.split('lib = l', 1)[1])
    if len(matches) != 1:
        raise ValueError('missing/ambiguous current-sequence program')
    equal(matches[0], 'primitive CurrentIndex >>> assert (primitive InputSequence)', 'literal program')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    parser.require(primitive, 'CurrentIndex :: Prim () Word32', 'index primitive type')
    line(primitive, 'primName CurrentIndex', '"currentIndex"')
    line(primitive, 'interpret CurrentIndex', 'element . return . toWord32 . toInteger $ ix')
    parser.require(primitive, 'ix = envIx env', 'current index source')
    bit = read(repo / 'Haskell/Core/Simplicity/Programs/Bit.hs')
    line(bit, 'assert t', 't &&& unit >>> assertr cmrFail0 oh')
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    for start, expected in [('(>>>)', 'comp'), ('(&&&)', 'pair'), ('oh', 'take iden'),
                            ('fail0', 'fail (hash0, hash0)')]:
        line(core, start, expected)
    line(read(repo / 'Haskell/Core/Simplicity/MerkleRoot/Impl.hs'), 'cmrFail0',
         'commitmentRoot (fail0 :: CommitmentRoot () ())')
    line(read(repo / 'Haskell/Core/Simplicity/Digest.hs'), 'hash0', 'review (over be256) 0')
    port = read(coq / 'C/jet_elements_prim.v')
    parser.require(port, '| CurrentIndex => "currentIndex"', 'Coq primitive identity')
    parser.require(port, '| CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix))', 'Coq primitive interpretation')
    definition(coq / 'C/jet_elements_current_spec.v', 'elements_current_spec', '''
      elements_comp (Primitive.Combinators.prim Elements.CurrentIndex) (elements_assert_spec p)''')
    definition(coq / 'C/jet_elements_current_spec.v', 'elements_comp', 'Alg.Core.Combinators.comp p q')
    definition(coq / 'C/jet_elements_current_spec.v', 'elements_assert_spec', '''
      Alg.Core.Combinators.comp (Alg.Core.Combinators.pair t Alg.Core.Combinators.unit)
        (Alg.Assertion.Combinators.assertr assertion_cmr_fail0
          (Alg.Core.Combinators.take Alg.Core.Combinators.iden))''')
    definition(coq / 'C/jet_assertion_spec.v', 'assertion_hash0', '''
      Simplicity.Digest.Hash256
        [Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero] eq_refl''')
    definition(coq / 'C/jet_assertion_spec.v', 'assertion_cmr_fail0', '''
      @Alg.Assertion.Combinators.fail Ty.Unit Ty.Unit
        Simplicity.MerkleRoot.CommitmentRoot_Assertion_alg (assertion_hash0, assertion_hash0)''')
    definition(coq / 'C/jet_elements_current_jets.v', 'elements_current_sequence_spec',
               'elements_current_spec (@elements_input_sequence_spec alg)')
    definition(literal, 'elements_current_literal_result', '''
      match p (haskell_to_word 5 (Z.of_nat (Elements.envIx environment))) environment with
      | Some (inr value) => Some value | _ => None end''')
    definition(literal, 'elements_current_sequence_literal_spec',
               'elements_current_literal_result elements_input_sequence_literal_spec')
    statement = re.findall(r'Theorem elements_current_sequence_literal_local_spec\s*:(.*?)\bProof\.', read(literal), re.S)
    if len(statement) != 1:
        raise ValueError('missing/ambiguous full C contract')
    equal(statement[0], '''
      application_jet_local_spec f_simplicity_current_sequence elements_ge Elements.env Ty.Unit Word32
        (current_scalar_rep (fun e => sigTxIn (Elements.envTx e))
          (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696)
        elements_current_sequence_literal_spec.''', 'C function/environment/representation/full contract')
    record.update({'selected_jet': 'CurrentSequence', 'current_index_assertion_reviewed': True})
    import hashlib
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'sequence', 'literal']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.sequence, args.literal), indent=2))
