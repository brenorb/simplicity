"""Read-only optional-issuance and original whole-contract corruption tests."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('issuance_amount_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
program = repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs'
local = coq / 'C/jet_elements_token_amount_literal.v'
old = coq / 'C/jet_elements_token_amount_jets.v'
current = old
helper = coq / 'C/jet_elements_token_amount_exec.v'
select = coq / 'C/jet_elements_token_select.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = [
    (hs, 'issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))',
         'issuanceTokenAmount = either newIssuanceTokenAmount reissuanceAmount'),
    (hs, 'encodeAmount . clearAmountPrf . issuanceTokenAmount', 'encodeAmount . issuanceTokenAmount'),
    (catalog, 'specificationTransaction IssuanceTokenAmount = primitive Prim.IssuanceTokenAmount',
              'specificationTransaction IssuanceTokenAmount = primitive Prim.IssuanceAssetAmount'),
    (program, 'currentIssuanceTokenAmount = primitive CurrentIndex >>> assert (primitive IssuanceTokenAmount)',
              'currentIssuanceTokenAmount = primitive CurrentIndex >>> assert (primitive IssuanceAssetAmount)'),
    (local, '(clearPrf (newIssuanceTokenAmount new))', '(clearPrf (newIssuanceAmount new))'),
    (local, 'Some (inr _) => inr (encode_amount_literal (Explicit Int64.zero))',
            'Some (inr _) => inr (encode_amount_literal (Explicit Int64.one))'),
    (local, 'None => inl tt', 'None => inr tt'),
    (local, '(Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64)',
            '(Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word32)'),
    (local, '(Ty.Sum Ty.Unit ConfAmount) 5', '(Ty.Sum Ty.Unit ConfAmount) 4'),
    (local, 'elements_current_literal_result elements_issuance_token_amount_literal_spec',
            'elements_current_literal_result elements_input_amount_literal_spec'),
    (helper, 'ibase + 272', 'ibase + 268'),
    (helper, 'ibase + 32', 'ibase + 36'),
    (select, 'inr _ => Explicit Int64.zero', 'inr _ => Explicit Int64.one'),
    (c, 'NEW_ISSUANCE == issuance->type ? &issuance->tokenAmt',
        'REISSUANCE == issuance->type ? &issuance->tokenAmt'),
    (c, '&(confAmount){ .prefix = EXPLICIT, .explicit = 0}',
        '&(confAmount){ .prefix = EXPLICIT, .explicit = 1}'),
    (c, 'issuanceTokenAmt(dst, &env->tx->input[i].issuance);',
        'issuanceTokenAmt(dst, &env->tx->input[0].issuance);'),
    (c, 'issuanceTokenAmt(dst, &env->tx->input[env->ix].issuance);',
        'issuanceTokenAmt(dst, &env->tx->input[0].issuance);'),
]
for iscur, path in [(False, old), (True, current)]:
    suffix = ('current_' if iscur else '') + 'issuance_token_amount'
    for file, name in [(path, 'elements_' + suffix + '_local_spec'),
                       (local, 'elements_' + suffix + '_literal_local_spec')]:
        text = file.read_text()
        start = text.index('Theorem ' + name)
        stop = text.index('Proof.', start)
        statement = text[start:stop]
        for a, b in [
            ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
            ('application_jet_local_spec_sep', 'application_jet_local_spec'),
            ('f_simplicity_' + suffix, 'f_simplicity_version'),
            ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
            ('issuance_token_rep', '(fun _ _ _ _ => True)'),
            ('544 256 0 696', '544 256 0 695'),
            ('Ty.Unit\n' if iscur else 'Word32\n', 'Word32\n' if iscur else 'Word16\n'),
            ('ConfAmount' if file == local else '(ConfTy Word64)', 'Word64')]:
            assert a in statement, (name, a)
            fixtures.append((file, statement, statement.replace(a, b, 1)))
original = Path.read_text
g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    assert a in text, ('inactive issuance amount fixture', path, a)
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
            raise AssertionError('accepted issuance amount source corruption: ' + a)
g.check(repo)
print(str(len(fixtures)) + ' issuance amount/branch/padding/representation/whole-C corruptions rejected')
