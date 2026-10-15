"""In-memory annex presence, hashing, representation and whole-contract mutations."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('annex_source_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
primitive = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
indexed, current = coq / 'C/jet_elements_annex_local.v', coq / 'C/jet_elements_current_gen_jets.v'
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction InputAnnexHash = primitive Prim.InputAnnexHash', 'specificationTransaction InputAnnexHash = primitive Prim.InputPegin'),
    (primitive, 'cast . fmap (encodeHash . bslHash) . sigTxiAnnex', 'cast . fmap encodeHash . sigTxiAnnex'),
    (primitive, 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'sigTxiAnnex :: Maybe BSL.ByteString', 'sigTxiAnnex :: BSL.ByteString'),
    (repo / 'Haskell/Core/Simplicity/Digest.hs', 'bslHash = ivHash . IV . pushChunks sha256Incremental . padSHA1', 'bslHash = bslDoubleHash'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentAnnexHash = primitive CurrentIndex >>> assert (primitive InputAnnexHash)', 'currentAnnexHash = primitive CurrentIndex >>> assert (primitive InputPegin)'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', 'currentAnnexHash = Transaction.currentAnnexHash Transaction.lib', 'currentAnnexHash = Transaction.currentPegin Transaction.lib'),
    (coq / 'C/jet_elements_prim.v', 'cast (option_map (fun x => encodeHash (byteStringHash x)) (sigTxiAnnex txi))', 'cast (option_map (fun x => encodeHash sha256_iv) (sigTxiAnnex txi))'),
    (indexed, 'map (fun txi => option_map byteStringHash (sigTxiAnnex txi))', 'map (fun txi => option_map (fun _ => sha256_iv) (sigTxiAnnex txi))'),
    (indexed, '(ofs + 536)', '(ofs + 537)'),
    (indexed, 'hash_elem_rep m b ofs h', 'hash_elem_rep m b (ofs + 32) h'),
    (indexed, 'txbase + 696', 'txbase + 704'),
    (current, 'flag_hash_rep annex_hash_of 536 0', 'flag_hash_rep annex_hash_of 537 32'),
    (coq / 'C/jet_elements_current_gen.v', '(be, ebase + 80, ebase + 88)', '(be, ebase + 72, ebase + 88)'),
    (literal, 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
    (literal, '| None => inl tt', '| None => inr (inl tt)'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, '(fun txi => option_map byteStringHash (sigTxiAnnex txi))', '(fun txi => Some (byteStringHash (match sigTxiAnnex txi with Some bytes => bytes | None => [] end)))'),
    (literal, 'elements_current_literal_result elements_input_annex_hash_literal_spec', 'elements_current_literal_result elements_input_pegin_literal_spec'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, 'flag_hash_rep annex_hash_of 536 0', 'flag_hash_rep annex_hash_of 537 0'),
    (literal, 'application_jet_local_spec_sep f_simplicity_input_annex_hash', 'application_jet_local_spec_sep f_simplicity_current_annex_hash'),
]
for prefix, file in [('input', indexed), ('current', current)]:
    for is_literal in [False, True]:
        path = literal if is_literal else file
        name = 'elements_' + prefix + '_annex_hash' + ('_literal' if is_literal else '') + '_local_spec'
        declaration = 'Theorem ' + name + ' :'
        fixtures.append((path, declaration, declaration + ' False ->'))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive annex mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted annex corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' annex optional-byte-hash/representation/whole-C-contract corruptions rejected')
