"""Read-only packed-field/asset/current/whole-C source corruptions."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('asset_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
spec = repo / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs'
program = repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs'
local = coq / 'C/jet_elements_asset_literal.v'
old = coq / 'C/jet_elements_asset_jets.v'
current = coq / 'C/jet_elements_current_input_jets.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = [
    (spec, 'fe_repr = toInteger . fe_pack', 'fe_repr = (`mod` fieldOrder) . toInteger . fe_pack'),
    (spec, 'data Point = Point Bool FE', 'data Point = Point Bool Word256'),
    (hs, 'toWord256 . Schnorr.fe_repr $ x', 'toWord256 . toInteger $ x'),
    (data, 'clearAssetPrf x = x & under asset . prf_ .~ ()', 'clearAssetPrf x = x'),
    (data, 'prf_ f (Confidential pt prf) = Confidential pt <$> f prf',
           'prf_ f (Confidential pt prf) = Confidential zeroPoint <$> f prf'),
    (local, 'Local Notation AssetConf := (ConfLiteral Word256)', 'Local Notation AssetConf := (ConfLiteral Word64)'),
    (local, 'haskell_word256_integer', 'haskell_word256_from_integer'),
    (local, 'if odd then inr tt else inl tt', 'if odd then inl tt else inr tt'),
    (local, 'encode_confidential_literal\n    (fun h => haskell_to_word 8', 'encode_confidential_literal\n    (fun h => haskell_to_word 7'),
    (local, '(fun txi => encode_asset_literal (utxoAsset (sigTxiTxo txi)))',
            '(fun txi => encode_asset_literal (utxoAsset (sigTxiTxo txi))) >>> iden'),
    (local, '(fun txo => encode_asset_literal (clearPrf (txoAsset txo)))',
            '(fun txo => encode_asset_literal (txoAsset txo))'),
    (local, 'elements_current_literal_result elements_input_asset_literal_spec',
            'elements_current_literal_result elements_output_asset_literal_spec'),
    (catalog, 'specificationTransaction CurrentAsset = Prog.currentAsset',
              'specificationTransaction CurrentAsset = Prog.currentAmount'),
    (program, 'currentAsset = primitive CurrentIndex >>> assert (primitive InputAsset)',
              'currentAsset = primitive CurrentIndex >>> assert (primitive InputAmount)'),
    (hs, 'cond = fromIntegral ix < Vector.length (sigTxIn tx)',
         'cond = fromIntegral ix <= Vector.length (sigTxIn tx)'),
    (old, 'if odd then Int.repr 3 else Int.repr 2', 'if odd then Int.repr 2 else Int.repr 3'),
    (old, 'hash256_reg (match a with Explicit h => h | Confidential (Point _ x) _ => x end)',
          'hash256_reg (match a with Explicit h => h | Confidential (Point _ x) _ => zeroHash end)'),
    (old, 'Mem.load Mint32 m b (ofs + 32)', 'Mem.load Mint32 m b (ofs + 28)'),
    (c, 'EXPLICIT == asset->prefix', 'EXPLICIT != asset->prefix'),
    (c, 'asset(dst, &env->tx->input[i].txo.asset);', 'asset(dst, &env->tx->input[i].txo.amt);'),
    (c, 'asset(dst, &env->tx->output[i].asset);', 'asset(dst, &env->tx->output[i].nonce);'),
    (c, 'asset(dst, &env->tx->input[env->ix].txo.asset);', 'asset(dst, &env->tx->input[0].txo.asset);'),
]
for suffix, path in [('input', old), ('output', old), ('current', current)]:
    for file, name in [(path, 'elements_' + suffix + '_asset_local_spec'),
                       (local, 'elements_' + suffix + '_asset_literal_local_spec')]:
        text = file.read_text()
        start = text.index('Theorem ' + name)
        stop = text.index('Proof.', start)
        statement = text[start:stop]
        for a, b in [
            ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
            ('application_jet_local_spec_sep', 'application_jet_local_spec'),
            ('f_simplicity_' + suffix + '_asset', 'f_simplicity_version'),
            ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
            ('asset_rep m b ofs', '(fun _ _ _ _ => True) m b ofs'),
            ('248 0 8 704' if suffix == 'output' else '544 168 0 696',
             '248 4 8 704' if suffix == 'output' else '544 164 0 696'),
            ('Ty.Unit\n' if suffix == 'current' else 'Word32\n',
             'Word32\n' if suffix == 'current' else 'Word16\n')]:
            assert a in statement, (name, a)
            fixtures.append((file, statement, statement.replace(a, b, 1)))
original = Path.read_text
g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    assert a in text, ('inactive asset fixture', path, a)
    altered = text.replace(a, b, 1)
    assert altered != text
    def read(self, *args, **kw):
        return altered if self == path else original(self, *args, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted asset source corruption: ' + a)
g.check(repo)
print(str(len(fixtures)) + ' packed-field/asset/current/representation/whole-C corruptions rejected')
