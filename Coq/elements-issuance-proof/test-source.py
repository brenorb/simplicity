"""In-memory mutations of issuance cases, selected source ports and whole contracts."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('issuance_source_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
primitive = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
port = coq / 'C/jet_elements_prim.v'
fixtures = [
    (primitive, 'just_ f = some_ f', 'just_ f = id'),
    (primitive, 'issuanceAmount = either newIssuanceAmount reissuanceAmount', 'issuanceAmount = either newIssuanceTokenAmount reissuanceAmount'),
    (primitive, 'issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))', 'issuanceTokenAmount = either newIssuanceTokenAmount reissuanceAmount'),
    (primitive, 'to sigTxiIssuance.just_.to issuanceAmount.under amount.prf_', 'to sigTxiIssuance.just_.to issuanceTokenAmount.under amount.prf_'),
    (primitive, 'to sigTxiIssuance.just_.to issuanceTokenAmount.under amount.prf_', 'to sigTxiIssuance.just_.to issuanceAmount.under amount.prf_'),
    (primitive, 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (data, 'prf_ f (Explicit x) = pure (Explicit x)', 'prf_ f (Explicit x) = f x'),
    (data, 'prf_ f (Confidential pt prf) = Confidential pt <$> f prf', 'prf_ f (Confidential pt prf) = pure (Confidential pt prf)'),
    (data, 'to (Amount x) = x', 'to (Amount x) = Explicit 0'),
    (data, 'type RangeProof = BSL.ByteString', 'type RangeProof = BS.ByteString'),
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction IssuanceAssetProof = primitive Prim.IssuanceAssetProof', 'specificationTransaction IssuanceAssetProof = primitive Prim.IssuanceTokenProof'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'currentIssuanceTokenProof = primitive CurrentIndex >>> assert (primitive IssuanceTokenProof)', 'currentIssuanceTokenProof = primitive CurrentIndex >>> primitive IssuanceTokenProof'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', 'currentIssuanceAssetProof = Transaction.currentIssuanceAssetProof Transaction.lib', 'currentIssuanceAssetProof = Transaction.currentIssuanceTokenProof Transaction.lib'),
    (port, '| Explicit _ => []', '| Explicit _ => [Byte.zero]'),
    (port, '| inr _ => Explicit Int64.zero', '| inr re => reissuanceAmount re'),
    (port, '| Some i => viewPrf (f i)', '| Some i => []'),
    (port, 'encodeHash (byteStringHash (issuanceProof issuanceAmount txi))', 'encodeHash (byteStringHash (issuanceProof issuanceTokenAmount txi))'),
    (port, 'encodeHash (byteStringHash (issuanceProof issuanceTokenAmount txi))', 'encodeHash (byteStringHash (issuanceProof issuanceAmount txi))'),
    (coq / 'C/jet_elements_input_hash_jets.v', '544 360 0 696', '544 392 0 696'),
    (coq / 'C/jet_elements_current_input_jets.v', '544 392 0 696', '544 360 0 696'),
    (literal, 'Explicit _ => []', 'Explicit _ => [Byte.zero]'),
    (literal, '| None => []', '| None => [Byte.zero]'),
    (literal, 'if token then [] else haskell_amount_proof_view', 'if token then haskell_amount_proof_view (reissuanceAmount re) else haskell_amount_proof_view'),
    (literal, 'if token then newIssuanceTokenAmount new else newIssuanceAmount new', 'if token then newIssuanceAmount new else newIssuanceTokenAmount new'),
    (literal, 'haskell_issuance_proof_view false txi', 'haskell_issuance_proof_view true txi'),
    (literal, 'elements_input_digest_literal_spec (fun txi => byteStringHash (haskell_issuance_proof_view false txi))', 'elements_input_digest_literal_spec (fun txi => byteStringHash (haskell_issuance_proof_view true txi))'),
    (literal, 'elements_current_literal_result elements_issuance_token_proof_literal_spec', 'elements_current_literal_result elements_issuance_asset_proof_literal_spec'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, '544 360 0 696', '544 392 0 696'),
    (literal, 'application_jet_local_spec_sep f_simplicity_issuance_asset_proof', 'application_jet_local_spec_sep f_simplicity_issuance_token_proof'),
]
for prefix in ['', 'current_']:
    for part in ['asset', 'token']:
        for is_literal in [False, True]:
            file = literal if is_literal else coq / ('C/jet_elements_current_input_jets.v' if prefix else 'C/jet_elements_input_hash_jets.v')
            declaration = 'Theorem elements_' + prefix + 'issuance_' + part + '_proof' + ('_literal' if is_literal else '') + '_local_spec :'
            fixtures.append((file, declaration, declaration + ' False ->'))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive issuance source mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted issuance source corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' issuance empty-view/projection/representation/whole-C-contract corruptions rejected')
