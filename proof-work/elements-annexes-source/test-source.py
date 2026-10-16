"""Read-only negative fixtures for the original Elements annex-loop boundary."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('annexes_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('annexes_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active annex-loop declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')
for path, start, stop, _ in model['blocks']:
    code = original(repo / path)
    begin, end = code.index(start), code.index(stop, code.index(start))
    block = code[begin:end]
    add(path, block, block + '\nUNREVIEWED_ACTIVE_CLAUSE\n')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
lib = 'Haskell/Core/Simplicity/Programs/Elements/Lib.hs'
elements = 'Haskell/Core/Simplicity/Programs/Elements.hs'
generic = 'Coq/C/jet_sha_hash_elems_reader.v'
endpoint = 'Coq/C/jet_elements_annexes_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash InputAnnexesHash = SigHash.inputAnnexesHash',
     'specificationSigHash InputAnnexesHash = SigHash.inputSequencesHash'),
    (catalog, 'InputAnnexesHash :: SigHashJet () Word256', 'InputAnnexesHash :: SigHashJet Word32 Word256'),
    (wrapper, 'inputAnnexesHash = SigHash.inputAnnexesHash SigHash.lib',
     'inputAnnexesHash = SigHash.inputAnnexesHash wrongLib'),
    (prim, 'InputAnnexHash :: Prim Word32 (S (S Word256))', 'InputAnnexHash :: Prim Word32 (S Word256)'),
    (prim, 'primName InputAnnexHash = "inputAnnexHash"', 'primName InputAnnexHash = "inputAnnex Hash"'),
    (prim, 'cast . fmap (encodeHash . bslHash) . sigTxiAnnex', 'cast . fmap encodeHash . sigTxiAnnex'),
    (prim, 'primPrefix = "Elements"', 'primPrefix = "Elements "'),
    (lib, 'annexHash = Elements.annexHash Elements.libAssert', 'annexHash = Elements.annexHash wrongLib'),
    (elements, 'ctx8Add32 = ctx8Addn vector32', 'ctx8Add32 = ctx8Addn vector64'),
    (elements, 'libAssert = mkLibAssert Sha256.lib Sha256.libAssert LibSecp256k1.lib',
     'libAssert = mkLibAssert Sha256.lib wrongLib LibSecp256k1.lib'),
    (elements, '((ih &&& (unit >>> scribe (toWord8 0x01)) >>> ctx8Add1) &&& oh >>> ctx8Add32)',
     '((ih &&& (unit >>> scribe (toWord8 0x02)) >>> ctx8Add1) &&& oh >>> ctx8Add32)'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     'body = take (drop (primitive InputAnnexHash)) &&& ih',
     'body = take (drop (primitive InputScriptSigHash)) &&& ih'),
    ('Haskell/Simplicity/Elements/Programs/SigHash.hs',
     '(injr (ih &&& oh >>> annexHash))', '(injr (ih &&& oh >>> ctx8Add32))'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->inputAnnexesHash);',
     'writeHash(dst, &env->tx->inputSequencesHash);'),
    (generic, 'Variable E : Type.', 'Variable E : Set.'),
    (generic, 'Hypothesis add_parametric : Alg.Assertion.Parametric add.',
     'Hypothesis add_parametric : False.'),
    (generic, 'Hypothesis add_option : forall c x, add optalg (c, x) = ctx8_add_list c (bytes_of x).',
     'Hypothesis add_option : forall c x, add optalg (c, x) = Some c.'),
    (generic, 'gen_bytes X bytes_of (firstn (Z.to_nat (wsize w)) xs)', 'gen_bytes X bytes_of xs'),
    (generic, '(forall x, Z.of_nat (length (bytes_of x)) <= N)', '(forall x, Z.of_nat (length (bytes_of x)) < N)'),
    (endpoint, '| None => inl tt', '| None => inr (from_hash256 (byteStringHash []))'),
    (endpoint, 'byteStringHash bs', 'byteStringHash []'),
    (endpoint, '(fun term => @annex_hash_spec term)', '(fun term => @ctx8_addn_spec 5 term)'),
    ('Coq/C/jet_bitcoin_tx_hash.v', '| inl _ => [byte_zero]', '| inl _ => []'),
    ('Coq/C/jet_bitcoin_tx_hash.v', '| inr h => byte_one :: vector_values (Word 3) 5 h',
     '| inr h => vector_values (Word 3) 5 h'),
    ('Coq/C/jet_bitcoin_ctx_hash_spec.v', '@fromZ (WordToZ 3) 1', '@fromZ (WordToZ 3) 2'),
]:
    add(path, a, b)

parser = g.load('annexes_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement',
                  'elements_input_annexes_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_input_annexes_hash', 'f_simplicity_input_sequences_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_input_annexes_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('0 376 760', '0 344 760'),
    ('elements_input_annexes_hash_spec', 'elements_prim_words_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete annexes contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))

for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op annex-loop fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted annex-loop source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements annex-loop/primitive/marker/Reader/C/full-contract corruptions rejected')
