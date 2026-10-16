"""Read-only canonical TapLeaf program/helper/contract corruption tests."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
original = Path.read_text
model = json.loads((HERE / 'source-model.json').read_text())
fixtures = []

for path, kind, name, _ in model['declarations']:
    # Exact active typed declaration, not a proof/comment/look-alike occurrence.
    parser = g.load('tapleaf_fixture_parser', repo / 'Coq/check-secp-predicates-specification.py')
    block = g.extract(parser.read_code(repo / path), kind, name).strip()
    fixtures.append((repo / path, block, block.replace(name, name + '_UNREVIEWED', 1)))
for path, start, stop, _ in model['blocks']:
    text = original(repo / path)
    begin, end = text.index(start), text.index(stop, text.index(start))
    block = text[begin:end]
    fixtures.append((repo / path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n'))

for path, a, b in [
    ('Haskell/Simplicity/Bitcoin/Jets.hs', 'specificationSigHash TapleafHash = SigHash.tapleafHash',
     'specificationSigHash TapleafHash = SigHash.tappathHash'),
    ('Haskell/Simplicity/Bitcoin/Programs/SigHash/Lib.hs', 'tapleafHash = SigHash.tapleafHash SigHash.lib',
     'tapleafHash = SigHash.tapleafHash otherLib'),
    ('Haskell/Simplicity/Bitcoin/Programs/SigHash.hs', 'ctx8InitTag "TapLeaf"', 'ctx8InitTag "TapData"'),
    ('Haskell/Simplicity/Bitcoin/Programs/SigHash.hs', 'scribe (toWord8 32)', 'scribe (toWord8 31)'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs', 'primPrefix = "Bitcoin"', 'primPrefix = "BitcoinExt"'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs', 'primName TapleafVersion = "tapleafVersion"', 'primName TapleafVersion = "tapleaf_version"'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs', 'interpret TapleafVersion = element . return . toWord8 . toInteger . tapleafVersion $ envTap env',
     'interpret TapleafVersion = element . return . toWord8 . toInteger . tapleafVersion $ otherTap env'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs', 'interpret ScriptCMR = element . return . toWord256 . integerHash256 . tapScriptCMR $ envTap env',
     'interpret ScriptCMR = element . return . toWord256 . integerHash256 . tapScriptCMR $ otherTap env'),
    ('Haskell/Core/Simplicity/Digest.hs', 'compress noTagIv (tagDigest, tagDigest)', 'compress noTagIv (tagDigest, hash0)'),
    ('Haskell/Core/Simplicity/Digest.hs', 'bsHash . BSC.pack $ tag', 'bsHash . BSC.pack $ reverse tag'),
    ('Haskell/Core/Simplicity/Digest.hs', 'noTagIv = IV sha256Incremental', 'noTagIv = IV otherIncremental'),
    ('Haskell/Core/Simplicity/Digest.hs', 'bsHash = bslHash . BSL.fromStrict', 'bsHash = bslDoubleHash . BSL.fromStrict'),
    ('Haskell/Core/Simplicity/Digest.hs', 'state `pushChunk` BSS.fromShort (hash256 h1) `pushChunk` BSS.fromShort (hash256 h2)',
     'state `pushChunk` BSS.fromShort (hash256 h2) `pushChunk` BSS.fromShort (hash256 h1)'),
    ('Coq/C/jet_bitcoin_tapleaf_literal.v', '[84; 97; 112; 76; 101; 97; 102]', '[84; 97; 112; 68; 97; 116; 97]'),
    ('Coq/C/jet_bitcoin_tapleaf_literal.v', '(haskell_to_word 3 32)', '(haskell_to_word 3 31)'),
    ('Coq/C/jet_bitcoin_tapleaf_literal.v', '(@ctx8_addn_spec 1 term)', '(@ctx8_addn_spec 2 term)'),
    ('Coq/C/jet_bitcoin_ext_prim.v', '0 <= extTapleafVersion < 256', '0 <= extTapleafVersion < 128'),
    ('Coq/C/jet_bitcoin_hash_getter_local.v', 'uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e))', 'True'),
    ('Coq/C/jet_sha_finalize_spec.v', '(@sha256_count_assertion_spec term)', '(@AC.unit _ (Alg.Assertion.toCore term))'),
    ('C/bitcoin/bitcoinJets.c', 'writeHash(dst, &env->taproot->tapLeafHash);', 'writeHash(dst, &env->taproot->scriptCMR);')]:
    fixtures.append((repo / path, a, b))

for path, kind, name, _ in model['declarations']:
    if name not in ['bitcoin_tapleaf_hash_literal_local_spec', 'bitcoin_tapleaf_hash_local_spec']:
        continue
    block = g.extract(parser.read_code(repo / path), kind, name).strip()
    for a, b in [('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                 ('f_simplicity_bitcoin_tapleaf_hash', 'f_simplicity_bitcoin_tappath_hash'),
                 ('bitcoin_ge ext_environment', 'ge0 ext_environment'),
                 ('Ty.Unit Word256', 'Word32 Word256'), ('8 8 176', '8 104 176'),
                 ('hash_getter_rep tapleaf_hash_of', '(fun _ _ _ _ => True)')]:
        assert a in block
        fixtures.append((repo / path, block, block.replace(a, b, 1)))

g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    assert a in text, ('inactive tapleaf fixture', path, a)
    altered = text.replace(a, b, 1)
    assert altered != text
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
print(str(len(fixtures)) + ' canonical TapLeaf program/tag/primitive/SHA-helper/whole-C source corruptions rejected')
