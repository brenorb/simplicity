"""Canonical amount/asset routing and exact original C pair contracts.

Not field arithmetic, host-library verification, caller construction, or normal
acceptance. Amount primitives and amount jets deliberately have different types.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def check(repo):
    coq = repo / 'Coq'
    prior = load('amount_shared_asset_source', HERE.parent / 'elements-asset-literal/check-source.py')
    r = prior.check(repo)
    p = load('amount_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('amount source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous amount clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous amount definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole amount contract: ' + name)
        equal(found[0], expected, name)

    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    p.require(data, 'import Data.Word (Word64, Word32, Word16, Word8)', 'native unsigned amount carrier')
    p.require(data, 'type Value = Word64', 'amount value width')
    p.require(data, 'newtype AmountWith prf = Amount (Confidential prf Value)', 'amount wrapper')
    line(data, 'clearAmountPrf x', 'x & under amount . prf_ .~ ()')
    if data.count('\namount =') != 1 or data.count('clearAmountPrf ::') != 1:
        raise ValueError('ambiguous amount adapter')
    equal(data.split('\namount =', 1)[1].split('clearAmountPrf ::', 1)[0],
          'adapter to fro where to (Amount x) = x fro x = (Amount x)', 'amount adapter')
    line(hs, 'encodeAmount', 'encodeConfidential (toWord64 . toInteger) . view (under amount)')
    for tag, name, route in [('InputAmount', 'inputAmount', 'utxoAmount . sigTxiTxo'),
                             ('OutputAmount', 'outputAmount', 'clearAmountPrf . txoAmount')]:
        p.require(hs, tag + ' :: Prim Word32 (S (Conf Word64))', 'amount-only primitive type')
        p.require(catalog, tag + ' :: TransactionJet Word32 (S (Conf Word256, Conf Word64))', 'asset/amount jet type')
        line(catalog, 'specificationTransaction ' + tag, 'Prog.' + name)
        line(hs, 'primName ' + tag, '"' + name + '"')
        line(hs, 'interpret ' + tag, 'return . (at' + ('Input' if tag == 'InputAmount' else 'Output') +
             ' $ encodeAmount . ' + route + ')')
    p.require(catalog, 'CurrentAmount :: TransactionJet () (Conf Word256, Conf Word64)', 'current pair type')
    line(catalog, 'specificationTransaction CurrentAmount', 'Prog.currentAmount')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    for name in ['inputAmount', 'outputAmount', 'currentAmount']:
        line(library, name, 'Transaction.' + name + ' Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous amount program library')
    for name, expected in [
        ('inputAmount', 'primitive InputAmount &&& primitive InputAsset >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))'),
        ('outputAmount', 'primitive OutputAmount &&& primitive OutputAsset >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))'),
        ('currentAmount', 'primitive CurrentIndex >>> assert (inputAmount)')]:
        found = re.findall(r'(?ms)^\s*, ' + name + r'\s*=(.*?)(?=^\s*,|\Z)', program.split('lib = l', 1)[1])
        if len(found) != 1:
            raise ValueError('missing/ambiguous amount program: ' + name)
        equal(found[0], expected, name)
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    line(core, 'ih', 'drop iden')
    line(core, 'oh', 'take iden')

    port = coq / 'C/jet_elements_prim.v'
    definition(port, 'amountWith', 'confidential prf int64')
    definition(port, 'encodeAmount', 'encodeConfidential (fun v => fromZ (Int64.unsigned v) : tySem Word64) a')
    sem = p.definition(read(port), 'sem')
    for tag, following, expected in [
        ('InputAmount', 'InputScriptHash', 'atInput (fun txi => encodeAmount (utxoAmount (sigTxiTxo txi)))'),
        ('OutputAmount', 'OutputNonce', 'atOutput (fun txo => encodeAmount (clearPrf (txoAmount txo)))')]:
        p.require(read(port), '| ' + tag + ' : prim Word32 (S (Conf Word64))', 'Coq amount primitive type')
        if sem.count('| ' + tag + ' =>') != 1 or sem.count('| ' + following + ' =>') != 1:
            raise ValueError('ambiguous amount primitive')
        equal(sem.split('| ' + tag + ' =>', 1)[1].split('| ' + following + ' =>', 1)[0], expected, tag)

    old = coq / 'C/jet_elements_amount_jets.v'
    definition(old, 'elements_amount_pair_spec', '''Alg.Core.Combinators.comp (Alg.Core.Combinators.pair pm pa)
      (Alg.Core.Combinators.case (Alg.Core.Combinators.injl Alg.Core.Combinators.unit)
        (Alg.Core.Combinators.comp
          (Alg.Core.Combinators.pair (Alg.Core.Combinators.drop Alg.Core.Combinators.iden)
            (Alg.Core.Combinators.take Alg.Core.Combinators.iden))
          (Alg.Core.Combinators.case (Alg.Core.Combinators.injl Alg.Core.Combinators.unit)
            (Alg.Core.Combinators.injr Alg.Core.Combinators.iden))))''')
    definition(old, 'amount_rep', r'''match a with
      | Explicit v => Mem.load Mint64 m b ofs = Some (Vlong v)
      | Confidential (Point _ x) _ => uint32_array_at m b ofs (hash256_reg x) end /\
      Mem.load Mint32 m b (ofs + 32) = Some (Vint (conf_prefix a))''')
    definition(old, 'encode_amount', '''match a with
      | Explicit v => inr (@fromZ (WordToZ 6) (Int64.unsigned v))
      | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x) end''')
    definition(old, 'amount_pair_result', '''match nth_error elems (Z.to_nat (toZ a)) with
      | Some x => inr (encode_asset (ga x), encode_amount (gm x)) | None => inl tt end''')
    literal = coq / 'C/jet_elements_amount_literal.v'
    p.require(read(literal), 'Local Notation AmountPair := (Ty.Prod (ConfLiteral Word256) (ConfLiteral Word64)).', 'asset-first pair widths')
    p.require(read(literal), 'Local Notation ConfLiteral a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).', 'confidential sum shape')
    definition(literal, 'encode_amount_literal', 'encode_confidential_literal (fun v => haskell_to_word 6 (Int64.unsigned v)) a')
    definition(literal, 'amount_pair_literal', '''@word_indexed_value_literal X AmountPair 5
      (fun x => (encode_asset_literal (asset_of x), encode_amount_literal (amount_of x))) values a''')
    definition(literal, 'elements_input_amount_literal_spec', '''amount_pair_literal (sigTxIn (Elements.envTx environment))
      (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) a''')
    definition(literal, 'elements_output_amount_literal_spec', '''amount_pair_literal (sigTxOut (Elements.envTx environment))
      (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) a''')
    definition(literal, 'elements_current_amount_literal_spec', 'elements_current_literal_result elements_input_amount_literal_spec')
    current = coq / 'C/jet_elements_current_gen_jets.v'
    definition(current, 'elements_current_amount_spec', 'elements_current_spec (@elements_input_amount_spec alg)')
    definition(current, 'input_amount_elem_rep', r'''asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\
      amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi))''')
    definition(coq / 'C/jet_elements_current_gen.v', 'current_gen_rep', r'''
      exists be ebase bt txbase bin inbase nI ixv,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
        0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
        Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
        Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
        Mem.load Mint64 m be (ebase + 80) = Some (Vlong ixv) /\
        Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
        Int64.unsigned ixv = Z.of_nat (Elements.envIx environment) /\
        (forall j x, nth_error (elems_of environment) j = Some x ->
          elemrep m bin (inbase + sz * Z.of_nat j) x) /\
        fp = [(be, ebase, ebase + 8); (be, ebase + 80, ebase + 88);
              (bt, txbase + adelta, txbase + adelta + 8);
              (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))]''')
    for suffix in ['input', 'output', 'current']:
        iscur, isout = suffix == 'current', suffix == 'output'
        if not iscur:
            definition(old, 'elements_' + suffix + '_amount_spec', '''elements_amount_pair_spec
              (Primitive.Combinators.prim Elements.''' + suffix.capitalize() + '''Amount)
              (Primitive.Combinators.prim Elements.''' + suffix.capitalize() + '''Asset)''')
        rep = ('''(current_gen_rep (fun e => sigTxIn (Elements.envTx e)) input_amount_elem_rep 544 0 696) ''' if iscur else
          r'''(indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
            (fun m b ofs txo => asset_rep m b (ofs + 0) (clearPrf (txoAsset txo)) /\
              amount_rep m b (ofs + 104) (clearPrf (txoAmount txo))) 248 0 8 704) ''' if isout else
          r'''(indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
            (fun m b ofs txi => asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\
              amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi))) 544 0 0 696) ''')
        prefix = ': application_jet_local_spec_sep f_simplicity_' + suffix + '_amount elements_ge Elements.env '
        oldty = 'Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)) ' if iscur else 'Word32 (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) '
        newty = 'Ty.Unit AmountPair ' if iscur else 'Word32 (Ty.Sum Ty.Unit AmountPair) '
        statement(current if iscur else old, 'elements_' + suffix + '_amount_local_spec', prefix + oldty + rep +
            '(fun a environment => @elements_' + suffix + '_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).')
        statement(literal, 'elements_' + suffix + '_amount_literal_local_spec', prefix + newty + rep +
            'elements_' + suffix + '_amount_literal_spec.')

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    def cbody(name, expected):
        found = list(re.finditer(r'\b(?:bool|void)\s+' + re.escape(name) + r'\s*\([^)]*\)\s*\{', c))
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual amount C function')
        start, end, depth = found[0].end(), found[0].end(), 1
        while end < len(c) and depth:
            depth += (c[end] == '{') - (c[end] == '}')
            end += 1
        if depth:
            raise ValueError('unterminated C function')
        equal(c[start:end-1], expected, name)
    cbody('amt', '''if (writeBit(dst, EXPLICIT == amt->prefix)) {
      skipBits(dst, 1 + 256 - 64); simplicity_write64(dst, amt->explicit);
      } else { writeBit(dst, ODD_Y == amt->prefix); writeHash(dst, &amt->confidential); }''')
    for suffix, count, asset, amount in [('input', 'numInputs', 'input[i].txo.asset', 'input[i].txo.amt'),
                                       ('output', 'numOutputs', 'output[i].asset', 'output[i].amt')]:
        cbody('simplicity_' + suffix + '_amount', '''uint_fast32_t i = simplicity_read32(&src);
          if (writeBit(dst, i < env->tx->''' + count + ''')) {
            asset(dst, &env->tx->''' + asset + '''); amt(dst, &env->tx->''' + amount + ''');
          } else { skipBits(dst, 516); } return true;''')
    cbody('simplicity_current_amount', '''(void) src; if (env->tx->numInputs <= env->ix) return false;
      asset(dst, &env->tx->input[env->ix].txo.asset); amt(dst, &env->tx->input[env->ix].txo.amt); return true;''')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.InputAmount', 'Elements.OutputAmount', 'Elements.CurrentAmount'],
             primitive_and_jet_codomain_distinguished=True, canonical_pair_routing_reviewed=True,
             explicit_word64_and_padding_reviewed=True, whole_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
