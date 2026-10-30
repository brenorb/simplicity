"""Read-only amount/pair-routing/width/padding/full-contract corruptions."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('amount_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
program = repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs'
local = coq / 'C/jet_elements_amount_literal.v'
old = coq / 'C/jet_elements_amount_jets.v'
current = coq / 'C/jet_elements_current_gen_jets.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = [
    (data, 'type Value = Word64', 'type Value = Word32'),
    (data, 'clearAmountPrf x = x & under amount . prf_ .~ ()', 'clearAmountPrf x = x'),
    (hs, 'encodeAmount = encodeConfidential (toWord64 . toInteger)',
         'encodeAmount = encodeConfidential (toWord32 . toInteger)'),
    (catalog, 'specificationTransaction InputAmount = Prog.inputAmount',
              'specificationTransaction InputAmount = primitive Prim.InputAmount'),
    (catalog, 'specificationTransaction CurrentAmount = Prog.currentAmount',
              'specificationTransaction CurrentAmount = Prog.currentAsset'),
    (program, 'inputAmount = primitive InputAmount &&& primitive InputAsset',
              'inputAmount = primitive InputAsset &&& primitive InputAmount'),
    (program, 'outputAmount = primitive OutputAmount &&& primitive OutputAsset',
              'outputAmount = primitive OutputAmount'),
    (program, 'currentAmount = primitive CurrentIndex >>> assert (inputAmount)',
              'currentAmount = primitive CurrentIndex >>> assert (outputAmount)'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'ih = drop iden', 'ih = take iden'),
    (old, '(Alg.Core.Combinators.pair pm pa)', '(Alg.Core.Combinators.pair pa pm)'),
    (local, 'Local Notation AmountPair := (Ty.Prod (ConfLiteral Word256) (ConfLiteral Word64))',
            'Local Notation AmountPair := (Ty.Prod (ConfLiteral Word64) (ConfLiteral Word256))'),
    (local, 'haskell_to_word 6 (Int64.unsigned v)', 'haskell_to_word 5 (Int64.unsigned v)'),
    (local, '@word_indexed_value_literal X AmountPair 5', '@word_indexed_value_literal X AmountPair 4'),
    (local, '(encode_asset_literal (asset_of x), encode_amount_literal (amount_of x))',
            '(encode_amount_literal (amount_of x), encode_asset_literal (asset_of x))'),
    (local, 'elements_current_literal_result elements_input_amount_literal_spec',
            'elements_current_literal_result elements_output_amount_literal_spec'),
    (old, 'Mem.load Mint64 m b ofs = Some (Vlong v)', 'Mem.load Mint32 m b ofs = Some (Vint v)'),
    (current, 'amount_rep m b (ofs + 208)', 'amount_rep m b (ofs + 204)'),
    (coq / 'C/jet_elements_current_gen.v', 'Int64.unsigned ixv = Z.of_nat (Elements.envIx environment)',
                                           'Int64.unsigned ixv = 0'),
    (c, 'skipBits(dst, 1 + 256 - 64);', 'skipBits(dst, 256 - 64);'),
    (c, 'simplicity_write64(dst, amt->explicit);', 'simplicity_write32(dst, amt->explicit);'),
    (c, 'amt(dst, &env->tx->input[i].txo.amt);', 'amt(dst, &env->tx->input[i].txo.asset);'),
    (c, 'amt(dst, &env->tx->output[i].amt);', 'amt(dst, &env->tx->output[0].amt);'),
    (c, 'amt(dst, &env->tx->input[env->ix].txo.amt);', 'amt(dst, &env->tx->input[0].txo.amt);'),
]
for suffix, path in [('input', old), ('output', old), ('current', current)]:
    for file, name in [(path, 'elements_' + suffix + '_amount_local_spec'),
                       (local, 'elements_' + suffix + '_amount_literal_local_spec')]:
        text = file.read_text()
        start = text.index('Theorem ' + name)
        stop = text.index('Proof.', start)
        statement = text[start:stop]
        codomain = 'AmountPair' if file == local else '(Ty.Prod (ConfTy Word256) (ConfTy Word64))'
        relation = 'input_amount_elem_rep' if suffix == 'current' else 'amount_rep m b'
        offset = '544 0 696' if suffix == 'current' else '248 0 8 704' if suffix == 'output' else '544 0 0 696'
        for a, b in [
            ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
            ('application_jet_local_spec_sep', 'application_jet_local_spec'),
            ('f_simplicity_' + suffix + '_amount', 'f_simplicity_version'),
            ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
            (relation, '(fun _ _ _ _ => True)' if suffix == 'current' else '(fun _ _ _ _ => True) m b'),
            (offset, offset[:-1] + '5'),
            ('Ty.Unit\n' if suffix == 'current' else 'Word32\n',
             'Word32\n' if suffix == 'current' else 'Word16\n'),
            (codomain, 'Word64')]:
            assert a in statement, (name, a)
            fixtures.append((file, statement, statement.replace(a, b, 1)))
fee_literal = coq / 'C/jet_elements_fee_literal.v'
fee_compare = coq / 'C/jet_elements_fee_compare.v'
fee_caller = coq / 'C/jet_elements_fee_flag_caller.v'
fixtures += [
    (catalog, 'specificationTransaction OutputIsFee = Prog.outputIsFee',
              'specificationTransaction OutputIsFee = Prog.outputAmount'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs',
     'outputIsFee = Transaction.outputIsFee Transaction.lib',
     'outputIsFee = Transaction.outputAmount Transaction.lib'),
    (program, 'outputIsFee = outputAmount &&& (primitive OutputScriptHash',
              'outputIsFee = outputAmount &&& (primitive OutputAsset'),
    (hs, 'interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoScript)',
         'interpret OutputScriptHash = return . (atOutput $ encodeHash . bslHash . txoSurjectionProof)'),
    (c, 'return output->emptyScript && EXPLICIT == output->asset.prefix && EXPLICIT == output->amt.prefix;',
        'return EXPLICIT == output->asset.prefix && EXPLICIT == output->amt.prefix;'),
    (c, 'writeBit(dst, isFee(&env->tx->output[i]));',
        'writeBit(dst, true);'),
    (program, 'emptyHash = toWord256 . integerHash256 $ bsHash mempty',
              'emptyHash = toWord256 0'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'oih = take ih', 'oih = take oh'),
    (coq / 'C/jet_elements_prim.v',
     'OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))',
     'OutputScriptHash => atOutput (fun txo => encodeHash (byteStringHash []))'),
    (fee_literal, 'Z.to_nat(toZ a)', '0%nat'),
    (fee_caller, 'Z.to_nat (toZ a)', '0%nat'),
    (fee_literal, 'byteStringHash []', 'byteStringHash [Int.zero]'),
    (fee_literal, 'case Bit.false(drop(case Bit.false(drop iden)))',
                  'case Bit.true(drop(case Bit.false(drop iden)))'),
    (fee_literal, 'take(drop iden)&&&', 'take(take iden)&&&'),
    (fee_literal, 'equality_spec(Ty.Unit+Word256)core', 'equality_spec(Ty.Unit+Word128)core'),
    (fee_literal, 'Primitive.Combinators.prim Elements.OutputScriptHash',
                  'Primitive.Combinators.prim Elements.OutputAsset'),
    (fee_literal, 'Explicit _,Explicit _=>fee_script_hash_test o',
                  'Explicit _,Explicit _=>Bit.zero'),
    (fee_caller, 'match txoScript o with [] => true | _::_ => false end',
                 'match txoScript o with [] => false | _::_ => true end'),
    (fee_caller, '(ofs+241)', '(ofs+240)'),
    (fee_compare, 'Explicit _,Explicit _=>Datatypes.true|_,_=>Datatypes.false',
                  'Explicit _,_=>Datatypes.true|_,_=>Datatypes.false'),
]
text = fee_compare.read_text()
start = text.index('Theorem elements_output_fee_implementation_comparison:')
stop = text.index('Proof.', start)
whole = text[start:stop]
for old, new in [
    ('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
    ('f_simplicity_output_is_fee', 'f_simplicity_output_amount'),
    ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    ('processed_fee_rep 248 0 8 704', '(fun _ _ _ _ => True) 248 0 8 704'),
    ('txoScript o<>[] /\\', 'True /\\'),
    ('byteStringHash(txoScript o)=byteStringHash []', 'True'),
]:
    assert old in whole, old
    fixtures.append((fee_compare, whole, whole.replace(old, new, 1)))
original = Path.read_text
g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    assert a in text, ('inactive amount fixture', path, a)
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
            raise AssertionError('accepted amount source corruption: ' + a)
g.check(repo)
print(str(len(fixtures)) + ' amount/pair/width/padding/representation/whole-C corruptions rejected')
