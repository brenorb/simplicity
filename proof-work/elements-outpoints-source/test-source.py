"""Read-only outpoints loop/marker/word/primitive/C source corruptions."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('outpoints_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('outpoints_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active outpoints declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    code = original(repo / path)
    begin, end = code.index(start), code.index(stop, code.index(start))
    block = code[begin:end]
    add(path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
sig = 'Haskell/Simplicity/Elements/Programs/SigHash.hs'
core = 'Haskell/Core/Simplicity/Programs/Elements.hs'
endpoint = 'Coq/C/jet_elements_outpoints_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash InputOutpointsHash = SigHash.inputOutpointsHash',
     'specificationSigHash InputOutpointsHash = SigHash.inputSequencesHash'),
    (catalog, 'InputOutpointsHash :: SigHashJet () Word256', 'InputOutpointsHash :: SigHashJet Word32 Word256'),
    (wrapper, 'inputOutpointsHash = SigHash.inputOutpointsHash SigHash.lib',
     'inputOutpointsHash = SigHash.inputOutpointsHash wrongLib'),
    (prim, 'InputPegin :: Prim Word32 (S (S Word256))', 'InputPegin :: Prim Word32 (S Word256)'),
    (prim, 'InputPrevOutpoint :: Prim Word32 (S (Word256,Word32))', 'InputPrevOutpoint :: Prim Word32 (S (Word256,Word64))'),
    (prim, 'primName InputPegin = "inputPegin"', 'primName InputPegin = "input Pegin"'),
    (prim, 'primName InputPrevOutpoint = "inputPrevOutpoint"', 'primName InputPrevOutpoint = "input PrevOutpoint"'),
    (prim, 'return . (atInput $ cast . fmap encodeHash . sigTxiPegin)',
     'return . (atInput $ cast . fmap encodeHash . wrongPegin)'),
    (prim, 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)',
     'return . (atInput $ encodeOutpoint . wrongOutpoint)'),
    (prim, 'toWord32 . fromIntegral $ opIndex op', 'toWord64 . fromIntegral $ opIndex op'),
    ('Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs', ', opIndex :: Word32', ', opIndex :: Word64'),
    ('Haskell/Core/Simplicity/Programs/Elements/Lib.hs', 'outpointHash = Elements.outpointHash Elements.libAssert',
     'outpointHash = Elements.outpointHash wrongLib'),
    (core, 'ctx8Add4 = ctx8Addn vector4', 'ctx8Add4 = ctx8Addn vector8'),
    (core, 'outpointHash = ((oh &&& ioh >>> annexHash)', 'outpointHash = ((oh &&& ioh >>> wrongHash)'),
    (sig, 'body = take (drop (primitive InputPegin)) &&& (take (drop (primitive InputPrevOutpoint)) &&& ih)',
     'body = take (drop (primitive InputAnnexHash)) &&& (take (drop (primitive InputPrevOutpoint)) &&& ih)'),
    (sig, '>>> match (injl iih) (ioh &&& (oh &&& iih)', '>>> match (injr iih) (ioh &&& (oh &&& iih)'),
    (sig, '>>> match (injl iih) (injr (iih &&& (ioh &&& oh) >>> outpointHash)))',
     '>>> match (injr iih) (injr (iih &&& (ioh &&& oh) >>> outpointHash)))'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->inputOutpointsHash);',
     'writeHash(dst, &env->tx->inputUTXOsHash);'),
    (endpoint, 'annex_elem_bytes (fst x) ++', '[] ++'),
    (endpoint, 'vector_values Word8 2 (snd (snd x))', 'vector_values Word8 3 (snd (snd x))'),
    (endpoint, 'Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))', 'Int.signed (opIndex (sigTxiPreviousOutpoint txi))'),
    (endpoint, 'None => inl tt | Some h => inr (from_hash256 h)',
     'None => inr (from_hash256 Digest.sha256_iv) | Some h => inr (from_hash256 h)'),
    (endpoint, '69 * wsize 5 / 64 < ctx8_limit', '68 * wsize 5 / 64 < ctx8_limit'),
    (endpoint, '(@for_while_program 5 _ _ _ core (@elements_outpoints_body alg))',
     '(@for_while_program 3 _ _ _ core (@elements_outpoints_body alg))'),
]:
    add(path, a, b)

parser = g.load('outpoints_complete_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement', 'elements_input_outpoints_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_input_outpoints_hash', 'f_simplicity_input_utxos_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_input_outpoints_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('0 216 760', '0 312 760'),
    ('elements_input_outpoints_hash_spec', 'elements_input_annexes_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete outpoints contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))

for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op outpoints fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted outpoints source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements outpoints loop/early-exit/primitive/marker/word/C/full-contract corruptions rejected')
