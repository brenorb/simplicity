"""Read-only mutations of selected Elements stream programs and C contracts."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_stream_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('elements_stream_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active Elements stream fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    text = original(repo / path)
    begin, end = text.index(start), text.index(stop, text.index(start))
    block = text[begin:end]
    add(path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
primitive = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
for suffix, selector, prim, field in g.JETS:
    constructor = selector[0].upper() + selector[1:]
    clause = 'specificationSigHash ' + constructor + ' = SigHash.' + selector
    add(catalog, clause, clause + '_UNREVIEWED\n-- ' + clause)
    clause = selector + ' = SigHash.' + selector + ' SigHash.lib'
    add(wrapper, clause, clause.replace('SigHash.lib', 'otherLib'))
    add(catalog, constructor + ' :: SigHashJet () Word256', constructor + ' :: SigHashJet Word32 Word256')
    clause = 'interpret ' + prim + ' = ' + g.PRIMITIVES[prim]
    add(primitive, clause, clause + ' UNREVIEWED\n-- ' + clause)
    input_ty = 'Word8' if prim == 'Tappath' else 'Word32'
    output_ty = 'Word32' if prim == 'InputSequence' else 'Word256'
    clause = prim + ' :: Prim ' + input_ty + ' (S ' + output_ty + ')'
    add(primitive, clause, prim + ' :: Prim () ()')
    c = 'writeHash(dst, &env->' + field + ');'
    add('C/elements/elementsJets.c', c, 'writeHash(dst, &env->wrongHash); /* ' + c + ' */')

for path, a, b in [
    ('Coq/C/jet_elements_words_hash_program.v', 'hash_words_of k (firstn (Z.to_nat (wsize w)) xs)', 'hash_words_of k xs'),
    ('Coq/C/jet_elements_words_hash_program.v', 'byteStringHash (viewPrf (txoAmount o))', 'byteStringHash (viewPrf (txoAsset o))'),
    ('Coq/C/jet_elements_words_hash_program.v', 'byteStringHash (viewPrf (txoAsset o))', 'byteStringHash []'),
    ('Coq/C/jet_elements_words_hash_program.v', '(Int.unsigned (sigTxiSequence i))', '(Int.signed (sigTxiSequence i))'),
    ('Coq/C/jet_elements_words_hash_program.v', 'Module EFP := PrimitiveElements.Primitive.', 'Module EFP := PrimitiveBitcoinFull.Primitive.'),
    ('Coq/C/jet_elements_prim.v', '| Confidential _ p => p', '| Confidential _ p => []'),
    ('Coq/C/jet_elements_hash_getter_local.v', 'uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e))', 'True'),
    ('Coq/C/jet_sha_hash_words_reader.v', 'Definition hash_reader_alg (E : Type)', 'Definition hash_reader_alg (E : Set)'),
    ('Coq/C/jet_sha256_ctx8_init_spec.v', '(@Word.zero 6 term)', '(@Word.one 6 term)'),
    ('Coq/C/jet_sha_ctx8_spec.v', '| O => @ctx8_add1_spec term', '| O => @AC.drop _ _ _ (Alg.Assertion.toCore term) AC.iden'),
    ('Coq/C/jet_sha_finalize_spec.v', '(@sha256_count_assertion_spec term)', '(@AC.unit _ (Alg.Assertion.toCore term))'),
    (primitive, 'primPrefix = "Elements"', 'primPrefix = "Elements "'),
    (primitive, 'primName Tappath = "tappath"', 'primName Tappath = "tap path"'),
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'prf_ f (Explicit x) = pure (Explicit x)', 'prf_ f (Explicit x) = pure (Confidential x mempty)'),
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type SurjectionProof = BSL.ByteString', 'type SurjectionProof = Hash256'),
    ('Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'sigTxiSequence :: Word32', 'sigTxiSequence :: Word64'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs', 'hashWord256s8 = hashWord256s word8', 'hashWord256s8 = hashWord256s word32'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs', 'hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector4 word32 array >>> ctx8Finalize', 'hashWord32s array = iden &&& (unit >>> ctx8Init) >>> Sha256.hashLoop vector8 word32 array >>> ctx8Finalize'),
]:
    add(path, a, b)

p = g.load('elements_stream_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
path = 'Coq/C/jet_elements_words_hash_program.v'
for suffix, _, _, _ in g.JETS:
    name = 'elements_' + suffix + '_program_local_spec'
    block = g.extract(p.read_code(repo / path), 'statement', name).strip()
    for a, b in [
        ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
        ('f_simplicity_' + suffix, 'f_simplicity_wrong_jet'),
        ('elements_ge Elements.env', 'ge0 Elements.env'),
        ('Ty.Unit Word256', 'Word32 Word256'),
        ('hash_getter_rep', 'wrong_rep'),
        ('elements_hash_alg', 'wrong_alg'),
    ]:
        if a not in block:
            raise AssertionError('inactive complete Elements contract fixture: ' + name + ':' + a)
        add(path, block, block.replace(a, b, 1))

if g.compact('"Elements "') == g.compact('"Elements"'):
    raise AssertionError('string literal whitespace was erased')
for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op Elements stream fixture: ' + str(path) + ':' + a)
g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    if a not in text:
        raise AssertionError('inactive Elements stream fixture: ' + str(path) + ':' + a)
    altered = text.replace(a, b, 1)
    if altered == text:
        raise AssertionError('no-op Elements stream fixture')
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted Elements stream source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements stream/program/primitive/proof-view/SHA/getter/full-contract corruptions rejected')
