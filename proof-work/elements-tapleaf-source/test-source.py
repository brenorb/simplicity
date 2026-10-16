"""Read-only corruptions of the literal Elements tapleaf source boundary."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_tapleaf_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('elements_tapleaf_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active tapleaf declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    code = original(repo / path)
    begin, end = code.index(start), code.index(stop, code.index(start))
    block = code[begin:end]
    add(path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
digest = 'Haskell/Core/Simplicity/Digest.hs'
sha = 'Haskell/Core/Simplicity/Programs/Sha256.hs'
endpoint = 'Coq/C/jet_elements_tapleaf_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash TapleafHash = SigHash.tapleafHash',
     'specificationSigHash TapleafHash = SigHash.tappathHash'),
    (catalog, 'TapleafHash :: SigHashJet () Word256', 'TapleafHash :: SigHashJet Word32 Word256'),
    (wrapper, 'tapleafHash = SigHash.tapleafHash SigHash.lib', 'tapleafHash = SigHash.tapleafHash wrongLib'),
    (prim, 'TapleafVersion :: Prim () Word8', 'TapleafVersion :: Prim Word32 Word8'),
    (prim, 'ScriptCMR :: Prim () Word256', 'ScriptCMR :: Prim () Word64'),
    (prim, 'primName TapleafVersion = "tapleafVersion"', 'primName TapleafVersion = "tapleaf Version"'),
    (prim, 'primName ScriptCMR = "scriptCMR"', 'primName ScriptCMR = "script CMR"'),
    (prim, 'primPrefix = "Elements"', 'primPrefix = "Elements "'),
    (prim, 'element = const', 'element = wrongElement'),
    (prim, 'element . return . toWord8 . toInteger . tapleafVersion', 'element . return . toWord8 . toInteger . wrongVersion'),
    (prim, 'element . return . encodeHash . tapScriptCMR', 'element . return . encodeHash . wrongCMR'),
    (digest, 'tagIv tag = compress noTagIv (tagDigest, tagDigest)', 'tagIv tag = compress noTagIv (tagDigest, wrongDigest)'),
    (digest, 'tagDigest = bsHash . BSC.pack $ tag', 'tagDigest = bsHash . wrongPack $ tag'),
    (digest, 'noTagIv = IV sha256Incremental', 'noTagIv = IV wrongIV'),
    (digest, 'bsHash = bslHash . BSL.fromStrict', 'bsHash = bslDoubleHash . BSL.fromStrict'),
    (digest, 'pushEndOfInput state', 'pushEndOfInput wrongState'),
    (sha, 'ctx8InitTag tag = buffer63Empty &&& (one word64 &&& prefix)',
     'ctx8InitTag tag = buffer63Empty &&& (zero word64 &&& prefix)'),
    (sha, 'prefix = scribe . toWord256 . integerHash256 . ivHash . tagIv $ tag',
     'prefix = scribe . toWord256 . integerHash256 . ivHash . noTagIv $ tag'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs', 'Sha256.ctx8InitTag "TapLeaf/elements"',
     'Sha256.ctx8InitTag "TapLeaf"'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->taproot->tapLeafHash);',
     'writeHash(dst, &env->taproot->tappathHash);'),
    (endpoint, '[84; 97; 112; 76; 101; 97; 102; 47;', '[84; 98; 112; 76; 101; 97; 102; 47;'),
    (endpoint, '"TapLeaf/elements"%string', '"TapLeaf/elements "%string'),
    (endpoint, 'haskell_to_word 3 32', 'haskell_to_word 3 31'),
    (endpoint, 'compress Digest.sha256_iv elements_tapleaf_tag_digest elements_tapleaf_tag_digest',
     'compress Digest.sha256_iv elements_tapleaf_tag_digest Digest.sha256_iv'),
    (endpoint, 'hash256_to_bytelist elements_tapleaf_midstate', 'hash256_to_bytelist elements_tapleaf_tag_digest'),
    (endpoint, '(@ctx8_addn_spec 1 term)', '(@ctx8_addn_spec 2 term)'),
    (endpoint, '(@ctx8_addn_spec 5 term)', '(@ctx8_addn_spec 6 term)'),
    ('Coq/C/jet_bitcoin_tapleaf_hash_spec.v', 'AC.pair one64_spec (Alg.scribe prefix)',
     'AC.pair (@Word.zero 6 term) (Alg.scribe prefix)'),
]:
    add(path, a, b)

parser = g.load('tapleaf_complete_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement', 'elements_tapleaf_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_tapleaf_hash', 'f_simplicity_tappath_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_tapleaf_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('8 8 176', '8 40 176'),
    ('elements_tapleaf_hash_spec', 'elements_prim_words_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete tapleaf contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))

for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op tapleaf fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted tapleaf source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements tapleaf tag/primitive/word/SHA/C/full-contract corruptions rejected')
