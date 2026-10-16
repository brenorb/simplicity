"""Read-only mutations of the literal issuance-proof loop and full C contract."""
import importlib.util
from pathlib import Path
import re
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('issuance_proofs_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
model = g.load('issuance_proofs_negative_model', HERE / 'source-model.py').MODEL
original = Path.read_text
fixtures = []


def add(path, before, after):
    fixtures.append((repo / path, before, after))


for path, kind, name, _ in model['declarations']:
    head = re.search(r'\b(?:Definition|Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])", original(repo / path))
    if head is None:
        raise AssertionError('missing active issuance-proofs declaration fixture: ' + name)
    add(path, head[0], head[0] + '_UNREVIEWED')

for path, start, stop, body in model['blocks']:
    full = start + body + stop
    for before, after in [('primitive IssuanceAssetProof', 'primitive IssuanceTokenProof'),
                          ('primitive IssuanceTokenProof', 'primitive IssuanceAssetProof'),
                          ('forWhile word32', 'forWhile word8'),
                          ('ctx8Addn vector64', 'ctx8Addn vector32'),
                          ('match (injl iih)', 'match (injr iih)')]:
        if before not in body:
            raise AssertionError('inactive issuance-proofs loop fixture: ' + before)
        add(path, full, start + body.replace(before, after, 1) + stop)

catalog = 'Haskell/Simplicity/Elements/Jets.hs'
wrapper = 'Haskell/Simplicity/Elements/Programs/SigHash/Lib.hs'
prim = 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
endpoint = 'Coq/C/jet_elements_issuance_proofs_hash_program.v'
for path, a, b in [
    (catalog, 'specificationSigHash IssuanceRangeProofsHash = SigHash.issuanceRangeProofsHash',
     'specificationSigHash IssuanceRangeProofsHash = SigHash.inputsHash'),
    (catalog, 'IssuanceRangeProofsHash :: SigHashJet () Word256',
     'IssuanceRangeProofsHash :: SigHashJet Word32 Word256'),
    (wrapper, 'issuanceRangeProofsHash = SigHash.issuanceRangeProofsHash SigHash.lib',
     'issuanceRangeProofsHash = SigHash.issuanceRangeProofsHash wrongLib'),
    (prim, 'primName IssuanceAssetProof = "issuanceAssetProof"',
     'primName IssuanceAssetProof = "issuanceTokenProof"'),
    (prim, 'issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))',
     'issuanceTokenAmount = either newIssuanceTokenAmount reissuanceAmount'),
    ('C/elements/elementsJets.c', 'writeHash(dst, &env->tx->issuanceRangeProofsHash);',
     'writeHash(dst, &env->tx->issuanceTokenAmountsHash);'),
    (endpoint, '(@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)',
     '(@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof)'),
    (endpoint, '(@EFP.Combinators.prim _ _ alg Elements.IssuanceTokenProof)',
     '(@EFP.Combinators.prim _ _ alg Elements.IssuanceAssetProof)'),
    (endpoint, '(@ctx8_addn_spec 6 term)', '(@ctx8_addn_spec 5 term)'),
    (endpoint, 'Some i => viewPrf (match i with', 'Some i => rev (viewPrf (match i with'),
    (endpoint, 'from_hash256 (byteStringHash (elements_issuance_asset_proof_bytes txi))',
     'from_hash256 (byteStringHash (elements_issuance_token_proof_bytes txi))'),
    (endpoint, 'inr _ => Explicit Int64.zero', 'inr ri => reissuanceAmount ri'),
]:
    add(path, a, b)

parser = g.load('issuance_proofs_contract_fixture', repo / 'Coq/check-secp-predicates-specification.py')
block = g.extract(parser.read_code(repo / endpoint), 'statement', 'elements_issuance_range_proofs_hash_program_local_spec').strip()
for a, b in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_issuance_range_proofs_hash', 'f_simplicity_input_outpoints_hash'),
    ('elements_ge Elements.env', 'wrong_ge Elements.env'),
    ('Ty.Unit Word256', 'Word32 Word256'),
    ('hash_getter_rep elements_issuance_range_proofs_hash_of', 'hash_getter_rep wrong_hash_of'),
    ('0 536 760', '0 504 760'),
    ('elements_issuance_range_proofs_hash_spec', 'elements_input_outpoints_hash_spec'),
    ('elements_hash_alg', 'wrong_alg'),
]:
    if a not in block:
        raise AssertionError('inactive complete issuance-proofs contract fixture: ' + a)
    add(endpoint, block, block.replace(a, b, 1))

for path, a, b in fixtures:
    if a not in original(path) or a == b:
        raise AssertionError('inactive/no-op issuance-proofs fixture: ' + str(path) + ':' + a)
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
            raise AssertionError('accepted issuance-proofs source corruption: ' + str(path) + ':' + a)
g.check(repo)
print(str(len(fixtures)) + ' Elements issuance-proofs two-primitive/loop/raw-view/C/full-contract corruptions rejected')
