"""Reject optional-tag/index/hash/representation corruptions in memory."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pegin_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction InputPegin = primitive Prim.InputPegin', 'specificationTransaction InputPegin = primitive Prim.InputAnnexHash'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentPegin = primitive CurrentIndex >>> assert (primitive InputPegin)', 'currentPegin = primitive CurrentIndex >>> assert (primitive InputAnnexHash)'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'return . (atInput $ cast . fmap encodeHash . sigTxiPegin)', 'return . (atInput $ cast . fmap encodeHash . sigTxiAnnex)'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'encodeHash = toWord256 . integerHash256', 'encodeHash = toWord256 . toInteger'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (coq / 'C/jet_elements_prim.v', '| InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiPegin txi)))', '| InputPegin => atInput (fun txi => cast (option_map encodeHash (sigTxiAnnex txi)))'),
    (coq / 'C/jet_elements_pegin_local.v', '(ofs + 537)', '(ofs + 536)'),
    (coq / 'C/jet_elements_pegin_local.v', 'hash_elem_rep m b (ofs + 32)', 'hash_elem_rep m b (ofs + 64)'),
    (coq / 'C/jet_elements_pegin_local.v', 'txbase + 696', 'txbase + 704'),
    (coq / 'C/jet_elements_pegin_local.v', 'Theorem elements_input_pegin_hash_local_spec :', 'Theorem elements_input_pegin_hash_local_spec : False ->'),
    (coq / 'C/jet_elements_current_gen_jets.v', 'flag_hash_rep sigTxiPegin 537 32', 'flag_hash_rep sigTxiPegin 536 32'),
    (coq / 'C/jet_elements_current_gen.v', '(be, ebase + 80, ebase + 88)', '(be, ebase + 72, ebase + 88)'),
    (literal, 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
    (literal, '| None => inl tt', '| None => inr (inl tt)'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, 'elements_current_literal_result elements_input_pegin_literal_spec', 'elements_current_literal_result elements_input_sequence_literal_spec'),
    (literal, 'Theorem elements_current_pegin_literal_local_spec :', 'Theorem elements_current_pegin_literal_local_spec : False ->'),
    (literal, 'application_jet_local_spec_sep f_simplicity_input_pegin', 'application_jet_local_spec_sep f_simplicity_current_pegin'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, 'flag_hash_rep sigTxiPegin 537 32', 'flag_hash_rep sigTxiPegin 537 64'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive pegin corruption: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted pegin corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' pegin presence/index/hash/representation/whole-C-contract corruptions rejected')
