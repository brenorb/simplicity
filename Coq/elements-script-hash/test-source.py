"""In-memory script selection, digest, representation and whole-contract mutations."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('script_hash_source_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction InputScriptHash = primitive Prim.InputScriptHash', 'specificationTransaction InputScriptHash = primitive Prim.InputScriptSigHash'),
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction CurrentScriptSigHash = Prog.currentScriptSigHash', 'specificationTransaction CurrentScriptSigHash = Prog.currentScriptHash'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'encodeHash . bslHash . utxoScript . sigTxiTxo', 'encodeHash . bslHash . sigTxiScriptSig'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'encodeHash . bslHash . sigTxiScriptSig', 'encodeHash . bslHash . utxoScript . sigTxiTxo'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1', 'bslHash = bslDoubleHash'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', '(n `shiftL` 8)', '(n `shiftL` 16)'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type Script = BSL.ByteString', 'type Script = BS.ByteString'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentScriptHash = primitive CurrentIndex >>> assert (primitive InputScriptHash)', 'currentScriptHash = primitive CurrentIndex >>> assert (primitive InputScriptSigHash)'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentScriptSigHash = primitive CurrentIndex >>> assert (primitive InputScriptSigHash)', 'currentScriptSigHash = primitive CurrentIndex >>> primitive InputScriptSigHash'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', 'currentScriptHash = Transaction.currentScriptHash Transaction.lib', 'currentScriptHash = Transaction.currentScriptSigHash Transaction.lib'),
    (coq / 'Simplicity/Digest.v', 'process_msg SHA256.init_registers (generate_and_pad_alt x)', 'process_msg SHA256.init_registers (generate_and_pad_alt [])'),
    (coq / 'C/jet_elements_prim.v', '| InputScriptHash => atInput (fun txi => encodeHash (byteStringHash (utxoScript (sigTxiTxo txi))))', '| InputScriptHash => atInput (fun txi => encodeHash (byteStringHash (sigTxiScriptSig txi)))'),
    (coq / 'C/jet_elements_prim.v', '| InputScriptSigHash => atInput (fun txi => encodeHash (byteStringHash (sigTxiScriptSig txi)))', '| InputScriptSigHash => atInput (fun txi => encodeHash (byteStringHash (utxoScript (sigTxiTxo txi))))'),
    (coq / 'C/jet_elements_input_hash_jets.v', 'hash256_reg (byteStringHash (utxo_script_bytes txo))', 'hash256_reg (byteStringHash (sigTxiScriptSig txo))'),
    (coq / 'C/jet_elements_input_hash_jets.v', '544 136 0 696', '544 64 0 696'),
    (coq / 'C/jet_elements_current_input_jets.v', '544 64 0 696', '544 136 0 696'),
    (coq / 'C/jet_elements_indexed_ptr.v', 'txbase + cdelta', 'txbase + adelta'),
    (coq / 'C/jet_elements_current_ptr_jets.v', 'ebase + 80', 'ebase + 72'),
    (coq / 'C/jet_elements_current_ptr_jets.v', 'fp = [(bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))]', 'fp = []'),
    (literal, 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
    (literal, '| None => inl tt', '| None => inr (haskell_to_word 8 0)'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, 'elements_current_literal_result elements_input_script_hash_literal_spec', 'elements_current_literal_result elements_input_script_sig_hash_literal_spec'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, '544 64 0 696', '544 136 0 696'),
]
for suffix in ['input_script_hash', 'input_script_sig_hash', 'current_script_hash', 'current_script_sig_hash']:
    declaration = 'Theorem elements_' + suffix + '_literal_local_spec :'
    fixtures.append((literal, declaration, declaration + ' False ->'))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive script-hash source mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted script-hash corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' script-hash projection/digest/representation/whole-C-contract corruptions rejected')
