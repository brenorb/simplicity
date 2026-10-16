"""Read-only mutations of tapEnvHash composition, key representation and C."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapenv_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('tapenv_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active tapenv declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
native = 'Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs'
spec = 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs'
endpoint = 'Coq/C/jet_elements_tap_env_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash TapEnvHash = SigHash.tapEnvHash', 'specificationSigHash TapEnvHash = SigHash.tapleafHash'),
    (catalog, 'TapEnvHash :: SigHashJet () Word256', 'TapEnvHash :: SigHashJet Word32 Word256'),
    (wrapper, 'tapEnvHash = SigHash.tapEnvHash SigHash.lib', 'tapEnvHash = SigHash.tapEnvHash wrongLib'),
    (prim, 'InternalKey :: Prim () PubKey', 'InternalKey :: Prim () FE'),
    (prim, 'primName InternalKey = "internalKey"', 'primName InternalKey = "internal Key"'),
    (prim, 'interpret InternalKey = element . return . encodeKey . tapInternalKey $ envTap env',
     'interpret InternalKey = element . return . encodeKey . wrongKey $ envTap env'),
    (prim, 'encodeKey (Schnorr.PubKey x) = toWord256 . toInteger $ x',
     'encodeKey (Schnorr.PubKey x) = toWord256 . Schnorr.fe_repr $ x'),
    (prim, 'import qualified Simplicity.LibSecp256k1.Schnorr as Schnorr',
     'import qualified Simplicity.LibSecp256k1.Other as Schnorr'),
    (native, 'data PubKey = PubKey Word256', 'data PubKey = PubKey FE'),
    (native, 'import Simplicity.Word', 'import Simplicity.Ty.Word'),
    (spec, 'import Simplicity.LibSecp256k1.Schnorr',
     'import Simplicity.LibSecp256k1.Schnorr\ndata PubKey = PubKey FE'),
    ('Haskell/Core/Simplicity/Ty/LibSecp256k1.hs', 'type PubKey = Word256', 'type PubKey = FE'),
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'import Simplicity.LibSecp256k1.Schnorr',
     'import Simplicity.LibSecp256k1.Other'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     'tapEnvHash = (ctx8Init &&& tapleafHash >>> ctx8Addn vector32)',
     'tapEnvHash = (ctx8Init &&& tappathHash >>> ctx8Addn vector32)'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     '(tappathHash &&& primitive InternalKey) >>> ctx8Addn vector64',
     '(tappathHash &&& primitive ScriptCMR) >>> ctx8Addn vector64'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->taproot->tapEnvHash);',
     'writeHash(dst, &env->taproot->tapLeafHash);'),
    (endpoint, '(@elements_tapleaf_hash_spec alg)', '(@elements_prim_words_hash_spec 5 3 Elements.Tappath alg)'),
    (endpoint, '(@elements_prim_words_hash_spec 5 3 Elements.Tappath alg)',
     '(@elements_prim_words_hash_spec 5 5 Elements.Tappath alg)'),
    (endpoint, '(@EFP.Combinators.prim _ _ alg Elements.InternalKey)',
     '(@EFP.Combinators.prim _ _ alg Elements.ScriptCMR)'),
    (endpoint, '(@ctx8_addn_spec 6 term)', '(@ctx8_addn_spec 5 term)'),
    (endpoint, 'from_hash256 (elements_tapleaf_hash_of e)',
     'from_hash256 (elements_words_hash_of 5 3 (elements_tappath_words e))'),
    (endpoint, 'from_hash256 (tapInternalKey (Elements.envTap e))',
     'from_hash256 (tapScriptCMR (Elements.envTap e))'),
]:
    add(path, a, b)

parser = g.load('tapenv_complete_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement', 'elements_tap_env_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_tap_env_hash', 'f_simplicity_tapleaf_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_tap_env_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('8 72 176', '8 8 176'),
    ('elements_tap_env_hash_spec', 'elements_tapleaf_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete tapenv contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))

for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op tapenv fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted tapenv source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements tapenv composition/primitive/native-key/C/full-contract corruptions rejected')
