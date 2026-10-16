"""Read-only inputsHash composition, raw digest and complete C contract mutations."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('inputs_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('inputs_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Fixpoint|Let|Record|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active inputs declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
program = 'Haskell/Simplicity/Elements/Programs/SigHash.hs'
endpoint = 'Coq/C/jet_elements_inputs_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash InputsHash = SigHash.inputsHash',
     'specificationSigHash InputsHash = SigHash.inputOutpointsHash'),
    (catalog, 'InputsHash :: SigHashJet () Word256', 'InputsHash :: SigHashJet Word32 Word256'),
    (wrapper, 'inputsHash = SigHash.inputsHash SigHash.lib', 'inputsHash = SigHash.inputsHash wrongLib'),
    (program, 'inputsHash = (ctx8Init &&& (inputOutpointsHash &&& inputSequencesHash) >>> ctx8Addn vector64)',
     'inputsHash = (ctx8Init &&& (inputSequencesHash &&& inputOutpointsHash) >>> ctx8Addn vector64)'),
    (program, '&&& inputAnnexesHash >>> ctx8Addn vector32 >>> ctx8Finalize',
     '&&& inputAnnexesHash >>> ctx8Addn vector64 >>> ctx8Finalize'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->inputsHash);',
     'writeHash(dst, &env->tx->inputOutpointsHash);'),
    (endpoint, '(@elements_input_outpoints_hash_spec alg)', '(@elements_input_annexes_hash_spec alg)'),
    (endpoint, '(@elements_prim_words_hash_spec 2 5 Elements.InputSequence alg)',
     '(@elements_prim_words_hash_spec 2 5 Elements.InputScriptSigHash alg)'),
    (endpoint, '(@elements_input_annexes_hash_spec alg)', '(@elements_input_outpoints_hash_spec alg)'),
    (endpoint, '(@ctx8_addn_spec 6 term)', '(@ctx8_addn_spec 5 term)'),
    (endpoint, '(@ctx8_addn_spec 5 term)', '(@ctx8_addn_spec 6 term)'),
    (endpoint, 'from_hash256 (elements_input_outpoints_hash_of e)',
     'from_hash256 (elements_input_annexes_hash_of e)'),
    (endpoint, 'from_hash256 (elements_words_hash_of 2 5 (elements_input_sequences_words e))',
     'from_hash256 (elements_input_outpoints_hash_of e)'),
]:
    add(path, a, b)
parser = g.load('inputs_complete_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement', 'elements_inputs_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_inputs_hash', 'f_simplicity_input_outpoints_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_inputs_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('0 440 760', '0 216 760'),
    ('elements_inputs_hash_spec', 'elements_input_outpoints_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete inputs contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))
for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op inputs fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted inputs source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements inputs composition/component/raw-digest/C/full-contract corruptions rejected')
