"""Read-only source corruptions: nonce tags, native payload, loop and C."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('nonces_negative_source', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('nonces_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])",
                     original(repo / path))
    if head is None:
        raise AssertionError('missing nonce declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
primitive = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
serializer = 'Coq/C/jet_elements_nonce_hash_spec.v'
endpoint = 'Coq/C/jet_elements_nonces_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash OutputNoncesHash = SigHash.outputNoncesHash',
     'specificationSigHash OutputNoncesHash = SigHash.outputScriptsHash'),
    (catalog, 'OutputNoncesHash :: SigHashJet () Word256', 'OutputNoncesHash :: SigHashJet Word32 Word256'),
    ('Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs',
     'outputNoncesHash = SigHash.outputNoncesHash SigHash.lib',
     'outputNoncesHash = SigHash.outputNoncesHash wrongLib'),
    ('Haskell/Core/Simplicity/Programs/Elements/Lib.hs',
     'nonceHash = Elements.nonceHash Elements.libAssert', 'nonceHash = Elements.annexHash Elements.libAssert'),
    (primitive, 'primName OutputNonce = "outputNonce"', 'primName OutputNonce = "outputNonce "'),
    (primitive, 'interpret OutputNonce = return . (atOutput $ encodeNonce . txoNonce)',
     'interpret OutputNonce = return . (atInput $ encodeNonce . txoNonce)'),
    (primitive, 'encodeNonce = cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . nonce)',
     'encodeNonce = cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . asset)'),
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs',
     'newtype Nonce = Nonce { nonce :: Either (Bool, Word256) Hash256 }',
     'newtype Nonce = Nonce { nonce :: Either (Bool, Word64) Hash256 }'),
    ('Haskell/Core/Simplicity/Programs/Elements.hs',
     ', nonceHash = ih &&& oh', ', nonceHash = oh &&& ih'),
    ('Haskell/Core/Simplicity/Programs/Elements.hs',
     '(scribe (toWord8 0x02)) (scribe (toWord8 0x03))',
     '(scribe (toWord8 0x03)) (scribe (toWord8 0x02))'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     'body = take (drop (primitive OutputNonce)) &&& ih',
     'body = take (drop (primitive OutputScriptHash)) &&& ih'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     '>>> match (injl ih) (injr (ih &&& oh >>> nonceHash))',
     '>>> match (injr ih) (injl (ih &&& oh >>> nonceHash))'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->outputNoncesHash);',
     'writeHash(dst, &env->tx->outputScriptsHash);'),
    (serializer, 'nonce_byte_two : Ty.tySem Word8 := @fromZ (WordToZ 3) 2',
     'nonce_byte_two : Ty.tySem Word8 := @fromZ (WordToZ 3) 3'),
    (serializer, '| inl _ => [byte_zero]', '| inl _ => []'),
    (serializer, '@ctx8_tagged_word_spec 5 term', '@ctx8_tagged_word_spec 4 term'),
    (endpoint, 'Elements.OutputNonce', 'Elements.OutputScriptHash'),
    (endpoint, '| None => inl tt', '| None => inr (inr (from_hash256 zero_hash))'),
    (endpoint, '| Some (inl (odd, w)) => inr (inl ((if odd then inr tt else inl tt), from_hash256 w))',
     '| Some (inl (odd, w)) => inr (inl ((if odd then inl tt else inr tt), from_hash256 w))'),
    ('Coq/C/jet_sha_tagged_word_spec.v', '(@ctx8_addn_spec k term)', '(@ctx8_addn_spec 0 term)'),
]:
    add(path, a, b)
parser = g.load('nonces_complete_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement',
                  'elements_output_nonces_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_output_nonces_hash', 'f_simplicity_output_scripts_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_output_nonces_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('0 56 760', '0 88 760'),
    ('elements_output_nonces_hash_spec', 'elements_prim_words_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete nonce contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))
for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op nonce fixture: ' + str(path) + ':' + a)
g.check(repo)
for path, a, b in fixtures:
    altered = original(path).replace(a, b, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted nonce source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' nonce serializer/native-payload/primitive/loop/C/full-contract corruptions rejected')
