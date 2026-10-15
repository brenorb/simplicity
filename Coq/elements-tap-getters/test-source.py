"""In-memory source/representation/whole-contract mutations; no invalid proofs compiled."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tap_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
literal = coq / 'C/jet_elements_tap_getters_literal.v'
nullable = coq / 'C/jet_elements_tappath_nullable.v'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
fixtures = [
    (catalog, 'specificationTransaction InternalKey = primitive Prim.InternalKey',
     'specificationTransaction InternalKey = primitive Prim.ScriptCMR'),
    (catalog, 'specificationTransaction Tappath = primitive Prim.Tappath',
     'specificationTransaction Tappath = primitive Prim.InternalKey'),
    (hs, 'encodeKey (Schnorr.PubKey x) = toWord256 . toInteger $ x',
     'encodeKey (Schnorr.PubKey x) = toWord256 . Schnorr.fe_repr $ x'),
    (hs, 'element . return . encodeKey . tapInternalKey $ envTap env',
     'element . return . encodeHash . tapScriptCMR $ envTap env'),
    (hs, 'listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8',
     'listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord32'),
    (hs, 'listToMaybe . flip drop', 'listToMaybe . flip take'),
    (repo / 'Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs',
     'data PubKey = PubKey Word256', 'data PubKey = PubKey FE'),
    (repo / 'Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs',
     'put (PubKey x) = put x', 'put (PubKey x) = put (fe_pack x)'),
    (repo / 'Haskell/Core/Simplicity/Word.hs',
     'put a3 >> put a2 >> put a1 >> put a0', 'put a0 >> put a1 >> put a2 >> put a3'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'fromWord8 = fromWord word8', 'fromWord8 = fromWord word16'),
    (literal, 'haskell_word256_integer', 'haskell_word64_modulus'),
    (literal, 'haskell_be256_run (hash256_to_bytelist h)',
     'haskell_be256_run (hash256_to_bytelist sha256_iv)'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, 'word_indexed_digest_literal 3', 'word_indexed_digest_literal 5'),
    (literal, 'hd_error (skipn', 'hd_error (firstn'),
    (literal, 'haskell_from_word depth a', 'haskell_from_word depth (fromZ 0)'),
    (literal, '0 <= haskell_from_word 3 a < 256', '0 <= haskell_from_word 3 a < 65536'),
    (literal, '| None => inl tt', '| None => inr (from_hash256 sha256_iv)'),
    (nullable, 'elements_tappath_env_rep_bounded 128', 'elements_tappath_env_rep_bounded 255'),
    (nullable, 'elements_tappath_env_rep_bounded 255', 'elements_tappath_env_rep_bounded 128'),
    (nullable, 'length (tappath (Elements.envTap e)) <= limit', 'length (tappath (Elements.envTap e)) < limit'),
    (nullable, 'tbase + 168', 'tbase + 169'),
    (nullable, '(0 < Z.of_nat (length (tappath (Elements.envTap e))) ->', '(0 <= Z.of_nat (length (tappath (Elements.envTap e))) ->'),
    (nullable, 'hash_elem_rep m bp (pbase + 32 * Z.of_nat j) h', 'hash_elem_rep m bp (pbase + 16 * Z.of_nat j) h'),
    (nullable, '(be, ebase + 8, ebase + 16)', '(be, ebase + 8, ebase + 8)'),
    (nullable, '0 <= nn <= 255', '0 <= nn <= 128'),
    (nullable, '(length (tappath (Elements.envTap e)) <= 128)%nat', '(length (tappath (Elements.envTap e)) <= 255)%nat'),
]
for path, name in [
    (coq / 'C/jet_elements_hash_field_jets.v', 'elements_internal_key_local_spec'),
    (literal, 'elements_internal_key_literal_local_spec'),
    (nullable, 'elements_tappath_nullable_local_spec'),
    (nullable, 'elements_tappath_u8_local_spec'),
    (nullable, 'elements_tappath_bounded_local_spec'),
    (literal, 'elements_tappath_nullable_literal_local_spec'),
    (literal, 'elements_tappath_u8_literal_local_spec')]:
    text = path.read_text()
    start = text.index('Theorem ' + name)
    stop = text.index('Proof.', start)
    statement = text[start:stop]
    for old, new in [('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                     ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                     ('Word256', 'Word128')]:
        assert old in statement, (name, old)
        fixtures.append((path, statement, statement.replace(old, new, 1)))
    if name == 'elements_internal_key_literal_local_spec':
        fixtures.append((path, statement, statement.replace('8 104 176', '8 136 176', 1)))
    if name == 'elements_tappath_bounded_local_spec':
        fixtures.append((path, statement, statement.replace('limit <= 255', 'limit <= 256', 1)))
original = Path.read_text
g.check(repo)
for path, old, new in fixtures:
    text = original(path)
    assert old in text, ('inactive mutation', path, old)
    altered = text.replace(old, new, 1)
    def read(self, *a, **kw):
        return altered if self == path else original(self, *a, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted tap-getter corruption: ' + old)
g.check(repo)
print(str(len(fixtures)) + ' raw-key/byte-index/nullable-128/u8-bound/whole-contract corruptions rejected')
