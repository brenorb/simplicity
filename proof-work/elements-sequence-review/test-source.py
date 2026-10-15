"""Scoped in-memory sequence-source mutations; never run a bad Coq proof."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sequence_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTransaction InputSequence = primitive Prim.InputSequence',
     'specificationTransaction InputSequence = primitive Prim.Version'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
     'primPrefix = "Elements"', 'primPrefix = "Bitcoin"'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
     'atInput $ toWord32 . toInteger . sigTxiSequence', 'atInput $ toWord32 . toInteger . sigTxLock'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs',
     'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs',
     'sigTxiSequence :: Word32', 'sigTxiSequence :: Word64'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'return (a, b)', 'return (b, a)'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'put (i `div` 2)', 'put (i `div` 4)'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'word32 = vector32', 'word32 = vector16'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'vector32 = DoubleV vector16', 'vector32 = DoubleV vector8'),
    (repo / 'Haskell/Core/Simplicity/Ty/Bit.hs', 'toBit False = Left ()', 'toBit False = Right ()'),
    (coq / 'C/jet_haskell_word_conversion.v', '((hi, lo), final)', '((lo, hi), final)'),
    (coq / 'C/jet_haskell_word_conversion.v', 'fst (haskell_word_state n z)', 'snd (haskell_word_state n z)'),
    (coq / 'C/jet_elements_prim.v',
     '| InputSequence => atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))',
     '| InputSequence => atInput (fun txi => fromZ (Int.signed (sigTxiSequence txi)))'),
    (coq / 'C/jet_elements_prim.v', 'None => inl tt', 'None => inr tt'),
    (literal, 'Theorem elements_input_sequence_literal_local_spec :',
     'Theorem elements_input_sequence_literal_local_spec : False ->'),
    (literal, 'application_jet_local_spec_sep f_simplicity_input_sequence',
     'application_jet_local_spec_sep f_simplicity_num_inputs'),
    (literal, 'elements_ge Elements.env', 'ge0 Elements.env'),
    (literal, '544 248 0 696', '544 256 0 696'),
    (literal, 'Some txi => inr (haskell_to_word 5', 'Some txi => inr (haskell_to_word 4'),
    (literal, 'None => inl tt', 'None => inr tt'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs',
     'fromWordRec (fromWordRec i w hi) w lo', 'fromWordRec (fromWordRec i w lo) w hi'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'fromWord32 = fromWord word32', 'fromWord32 = fromWord word16'),
    (literal, 'haskell_from_word_acc k (haskell_from_word_acc k i hi) lo',
     'haskell_from_word_acc k (haskell_from_word_acc k i lo) hi'),
    (literal, 'haskell_from_word_acc n 0 a', 'haskell_from_word_acc n 1 a'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if text.count(old) < 1:
        raise AssertionError('inactive sequence fixture: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted sequence corruption: ' + old)
gate.check(repo, coq, literal)
print('24 sequence program/primitive/word-conversion/C-contract corruptions rejected')
