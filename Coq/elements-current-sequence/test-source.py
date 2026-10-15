"""In-memory source corruptions only; never compile an invalid proof."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('current_sequence_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, sequence, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, sequence, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTransaction CurrentSequence = Prog.currentSequence',
     'specificationTransaction CurrentSequence = Prog.currentScriptHash'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs',
     'currentSequence = Transaction.currentSequence Transaction.lib',
     'currentSequence = Transaction.currentScriptHash Transaction.lib'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs',
     'currentSequence = primitive CurrentIndex >>> assert (primitive InputSequence)',
     'currentSequence = primitive CurrentIndex >>> assert (primitive InputScriptHash)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Bit.hs',
     'assert t = t &&& unit >>> assertr cmrFail0 oh',
     'assert t = t &&& unit >>> assertl oh cmrFail0'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'oh = take iden', 'oh = drop iden'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', '(>>>) = comp', '(>>>) = pair'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', '(&&&) = pair', '(&&&) = comp'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'fail0 = fail (hash0, hash0)', 'fail0 = fail (hash1, hash0)'),
    (repo / 'Haskell/Core/Simplicity/MerkleRoot/Impl.hs',
     'cmrFail0 = commitmentRoot (fail0 :: CommitmentRoot () ())',
     'cmrFail0 = identityRoot (fail0 :: CommitmentRoot () ())'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'hash0 = review (over be256) 0', 'hash0 = review (over be256) 1'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
     'interpret CurrentIndex = element . return . toWord32 . toInteger $ ix',
     'interpret CurrentIndex = element . return . toWord32 . toInteger $ ix + 1'),
    (coq / 'C/jet_elements_prim.v',
     '| CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix))',
     '| CurrentIndex => fun _ => Some (fromZ (Z.of_nat ix + 1))'),
    (coq / 'C/jet_elements_current_spec.v',
     'elements_comp (Primitive.Combinators.prim Elements.CurrentIndex) (elements_assert_spec p)',
     'elements_comp (Primitive.Combinators.prim Elements.Version) (elements_assert_spec p)'),
    (coq / 'C/jet_elements_current_spec.v',
     'Alg.Assertion.Combinators.assertr assertion_cmr_fail0',
     'Alg.Assertion.Combinators.assertl assertion_cmr_fail0'),
    (literal, 'Theorem elements_current_sequence_literal_local_spec :',
     'Theorem elements_current_sequence_literal_local_spec : False ->'),
    (literal, 'application_jet_local_spec f_simplicity_current_sequence',
     'application_jet_local_spec f_simplicity_input_sequence'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, '544 248 0 696', '544 256 0 696'),
    (literal, 'Some (inr value) => Some value', 'Some (inl value) => Some value'),
    (literal, 'haskell_to_word 5 (Z.of_nat', 'haskell_to_word 4 (Z.of_nat'),
    (literal, '(Elements.envIx environment)', '(Elements.envIx environment + 1)%nat'),
    (literal, 'elements_current_literal_result elements_input_sequence_literal_spec',
     'elements_current_literal_result elements_input_script_hash_literal_spec'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive mutation fixture: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, sequence, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted corruption: ' + old)
gate.check(repo, coq, sequence, literal)
print(str(len(fixtures)) + ' CurrentSequence source/primitive/assertion/whole-C-contract corruptions rejected')
