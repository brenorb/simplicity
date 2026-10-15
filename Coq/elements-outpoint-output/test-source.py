"""Reject selected tuple, index, hash, footprint and whole-C-contract corruptions."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_source_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
primitive = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
indexed, current = coq / 'C/jet_elements_indexed_ptr_jets.v', coq / 'C/jet_elements_current_input_jets.v'
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction InputPrevOutpoint = primitive Prim.InputPrevOutpoint', 'specificationTransaction InputPrevOutpoint = primitive Prim.InputPegin'),
    (primitive, 'encodeOutpoint op = (encodeHash $ opHash op, toWord32 . fromIntegral $ opIndex op)', 'encodeOutpoint op = (toWord32 . fromIntegral $ opIndex op, encodeHash $ opHash op)'),
    (primitive, 'interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)', 'interpret OutputScriptHash = return . (atOutput $ encodeHash . txoScript)'),
    (primitive, 'lookupOutput = (sigTxOut tx !?) . fromIntegral', 'lookupOutput = (sigTxIn tx !?) . fromIntegral'),
    (primitive, 'atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord32', 'atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord16'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'opIndex :: Word32', 'opIndex :: Word64'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type Script = BSL.ByteString', 'type Script = Hash256'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentPrevOutpoint = primitive CurrentIndex >>> assert (primitive InputPrevOutpoint)', 'currentPrevOutpoint = primitive CurrentIndex >>> assert (primitive InputPegin)'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', 'currentPrevOutpoint = Transaction.currentPrevOutpoint Transaction.lib', 'currentPrevOutpoint = Transaction.currentPegin Transaction.lib'),
    (coq / 'C/jet_elements_prim.v', 'opIndex : int', 'opIndex : int64'),
    (coq / 'C/jet_elements_prim.v', '(encodeHash (opHash op), fromZ (Int.unsigned (opIndex op)) : tySem Word32)', '(encodeHash (opHash op), fromZ (Int.signed (opIndex op)) : tySem Word32)'),
    (coq / 'C/jet_elements_prim.v', '| OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))', '| OutputScriptHash => atOutput (fun txo => encodeHash sha256_iv)'),
    (indexed, 'Int64.repr (Int.unsigned (opIndex op))', 'Int64.repr (Int.signed (opIndex op))'),
    (indexed, 'Mem.load Mint64 m b (ofs + 32)', 'Mem.load Mint32 m b (ofs + 32)'),
    (indexed, 'uint32_array_at m b ofs (outpoint_words txi)', 'uint32_array_at m b (ofs + 4) (outpoint_words txi)'),
    (indexed, 'hash256_reg (byteStringHash (txoScript txo))', 'hash256_reg sha256_iv'),
    (coq / 'C/jet_elements_indexed_ptr.v', 'inbase + sz * Z.of_nat j + poff', 'inbase + sz * Z.of_nat j'),
    (coq / 'C/jet_elements_current_ptr_jets.v', 'Int64.unsigned ixv = Z.of_nat (ix_of environment)', 'True'),
    (coq / 'C/jet_elements_current_ptr_jets.v', 'fp = [(bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))]', 'fp = []'),
    (literal, 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, 'haskell_to_word 5 (Int.unsigned (opIndex op))', 'haskell_to_word 5 (Int.signed (opIndex op))'),
    (literal, '| None => inl tt | Some x => inr (encode x)', '| None => inr (encode x) | Some x => inl tt'),
    (literal, 'elements_current_literal_result elements_input_prev_outpoint_literal_spec', 'elements_current_literal_result elements_input_pegin_literal_spec'),
]
for name, origin in [('input_prev_outpoint', indexed), ('current_prev_outpoint', current), ('output_script_hash', indexed)]:
    for is_literal, path in [(False, origin), (True, literal)]:
        declaration = 'Theorem elements_' + name + ('_literal' if is_literal else '') + '_local_spec :'
        text = path.read_text()
        start, stop = text.index(declaration), text.index('Proof.', text.index(declaration))
        statement = text[start:stop]
        for old, new in [('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                         (declaration, declaration + ' False ->'),
                         ('544 96 0 696', '544 96 0 704') if 'outpoint' in name else ('248 180 8 704', '248 180 0 704'),
                         ('Ty.Prod Word256 Word32', 'Ty.Prod Word32 Word256') if 'outpoint' in name else ('Ty.Sum Ty.Unit Word256', 'Ty.Sum Ty.Unit Word128')]:
            if old not in statement:
                raise AssertionError('inactive selected contract fixture: ' + name)
            fixtures.append((path, statement, statement.replace(old, new, 1)))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive outpoint/output mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted outpoint/output corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' outpoint/output tuple/index/hash/footprint/whole-C-contract corruptions rejected')
