"""Read-only nonce/index/representation/whole-contract mutations."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('nonce_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
local = coq / 'C/jet_elements_output_nonce_literal.v'
old = coq / 'C/jet_elements_asset_jets.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = [
    (catalog, 'specificationTransaction OutputNonce = primitive Prim.OutputNonce',
              'specificationTransaction OutputNonce = primitive Prim.OutputAsset'),
    (hs, 'interpret OutputNonce = return . (atOutput $ encodeNonce . txoNonce)',
         'interpret OutputNonce = return . (atOutput $ encodeAsset . txoAsset)'),
    (hs, 'encodeNonce = cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . nonce)',
         'encodeNonce = cast . fmap (((toBit *** (toWord256 . Schnorr.fe_repr)) +++ encodeHash) . nonce)'),
    (data, 'nonce :: Either (Bool, Word256) Hash256', 'nonce :: Either (Bool, FE) Hash256'),
    (local, 'haskell_word256_integer', 'haskell_word256_from_integer'),
    (local, 'if odd then inr tt else inl tt', 'if odd then inl tt else inr tt'),
    (local, 'None => inl tt | Some v => inr (nonce_payload_literal v)',
            'None => inr (nonce_payload_literal v) | Some v => inl tt'),
    (local, 'haskell_from_word depth a', 'haskell_from_word depth a + 1'),
    (local, 'word_indexed_value_literal 5', 'word_indexed_value_literal 4'),
    (local, 'sigTxOut (Elements.envTx environment)', 'sigTxIn (Elements.envTx environment)'),
    (local, '4294967296', '65536'),
    (old, 'None => Int.repr 0 end', 'None => Int.repr 1 end'),
    (old, 'if odd then Int.repr 3 else Int.repr 2', 'if odd then Int.repr 2 else Int.repr 3'),
    (old, '(n <> None -> uint32_array_at m b ofs (nonce_words n))',
          'uint32_array_at m b ofs (nonce_words n)'),
    (coq / 'C/jet_elements_asset_helper.v', 'Some false :: repeat None 258', 'Some false :: repeat None 259'),
    (c, 'nonce(dst, &env->tx->output[i].nonce);', 'asset(dst, &env->tx->output[i].nonce);'),
    (c, 'NONE != nonce->prefix', 'NONE == nonce->prefix'),
    (c, 'skipBits(dst, 1+1+256);', 'skipBits(dst, 1+1+255);'),
    (repo / 'C/elements/txEnv.h', 'ODD_Y = 3', 'ODD_Y = 4'),
]
for file, name in [(old, 'elements_output_nonce_local_spec'),
                   (local, 'elements_output_nonce_literal_local_spec')]:
    text = file.read_text()
    start = text.index('Theorem ' + name)
    stop = text.index('Proof.', start)
    statement = text[start:stop]
    for old_text, new_text in [
        ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
        ('application_jet_local_spec_sep', 'application_jet_local_spec'),
        ('f_simplicity_output_nonce', 'f_simplicity_output_asset'),
        ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
        ('Elements.env Word32', 'Elements.env Word16'),
        ('248 144 8 704', '248 140 8 704'),
        ('nonce_rep m b ofs (txoNonce txo)', 'True')]:
        assert old_text in statement, (name, old_text)
        fixtures.append((file, statement, statement.replace(old_text, new_text, 1)))
original = Path.read_text
g.check(repo)
for path, old_text, new_text in fixtures:
    text = original(path)
    assert old_text in text, ('inactive nonce fixture', path, old_text)
    altered = text.replace(old_text, new_text, 1)
    assert altered != text
    def read(self, *a, **kw):
        return altered if self == path else original(self, *a, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted invalid nonce source: ' + old_text)
g.check(repo)
print(str(len(fixtures)) + ' nonce/word/index/padding/representation/whole-C corruptions rejected')
