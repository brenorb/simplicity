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


def check_fee(repo):
    """Anchor the unregistered fee programs/comparison; not jet equivalence."""
    coq = repo / 'Coq'
    p = load('fee_amount_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []
    def read(path):
        paths.append(path)
        return p.read_code(path)
    def equal(actual, expected, label):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('output fee source differs: ' + label)
    def line(source, name, expected):
        rows = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(rows) != 1:
            raise ValueError('missing/ambiguous fee clause: ' + name)
        equal(rows[0], expected, name)
    def definition(path, name, expected):
        equal(p.definition(read(path), name), expected, name)
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    rows = re.findall(r'(?ms)^\s*, outputIsFee\s*=(.*?)(?=^\s*,|\Z)', program.split('lib = l', 1)[1])
    if len(rows) != 1:
        raise ValueError('missing/ambiguous fee program')
    equal(rows[0], '''outputAmount &&& (primitive OutputScriptHash &&& scribe (Right emptyHash) >>> eq)
      >>> match (injl unit) (injr (oih &&& (ooh &&& ih)
       >>> match false (drop (match false ih))))''', 'canonical outputIsFee tree')
    line(program, 'emptyHash', 'toWord256 . integerHash256 $ bsHash mempty')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    p.require(catalog, 'OutputIsFee :: TransactionJet Word32 (S Bit)', 'fee type')
    line(catalog, 'specificationTransaction OutputIsFee', 'Prog.outputIsFee')
    p.require(catalog, 'TotalFee :: TransactionJet Word256 Word64', 'total fee type')
    line(catalog, 'specificationTransaction TotalFee', 'Prog.totalFee')
    line(read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs'),
         'outputIsFee', 'Transaction.outputIsFee Transaction.lib')
    line(read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'),
         'interpret OutputScriptHash', 'return . (atOutput $ encodeHash . bslHash . txoScript)')
    line(read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs'),
         'totalFee', 'Transaction.totalFee Transaction.lib')
    totals = re.findall(r'(?ms)^\s*, totalFee\s*=(.*?)(?=^\s*,|\Z)', program.split('lib = l', 1)[1])
    if len(totals) != 1:
        raise ValueError('missing/ambiguous total fee program')
    equal(totals[0], '''let
      body = take (drop outputIsFee) &&& (take (drop outputAmount) &&& (ooh &&& ih))
       >>> match (injl iiih)
        (injr (match iiih (drop (match iih
         ((ooh &&& (injr ioh) >>> eq) &&& (oih &&& iih)
          >>> (match iih (drop (match ih (add word64 >>> ih)))))))))
      in (iden &&& (unit >>> zero word64)) >>> forWhile word32 body >>> copair iden iden''',
      'canonical totalFee tree')
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    for name, expected in [('ih', 'drop iden'), ('oh', 'take iden'),
                           ('oih', 'take ih'), ('ooh', 'take oh'),
                           ('ioh', 'drop oh'), ('iih', 'drop ih'), ('iiih', 'drop iih')]:
        line(core, name, expected)
    prim = read(coq / 'C/jet_elements_prim.v')
    sem = p.definition(prim, 'sem')
    if sem.count('| OutputScriptHash =>') != 1:
        raise ValueError('ambiguous fee script-hash primitive')
    equal(sem.split('| OutputScriptHash =>', 1)[1].split('| OutputNullDatum =>', 1)[0],
          'atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))', 'script primitive semantics')
    literal = coq / 'C/jet_elements_fee_literal.v'
    for name, expected in [
        ('fee_empty_hash_word', 'haskell_to_word 8(haskell_integer_hash256(hash256_to_bytelist(byteStringHash [])))'),
        ('elements_fee_tail', '''case(injl unit)
          (injr((take(drop iden)&&&(take(take iden)&&&drop iden)) >>>
            case Bit.false(drop(case Bit.false(drop iden)))))'''),
        ('elements_output_fee_hash_eq', '''elements_comp
          (elements_pair(Primitive.Combinators.prim Elements.OutputScriptHash)
           (elements_core(fun core=>@Alg.scribe Word32(Ty.Unit+Word256)(inr fee_empty_hash_word)core)))
          (elements_core(fun core=>@equality_spec(Ty.Unit+Word256)core))'''),
        ('elements_output_fee_spec', '''elements_comp
          (elements_pair(@elements_output_amount_spec alg)(@elements_output_fee_hash_eq alg))
          (elements_core(fun core=>@elements_fee_tail core))'''),
        ('fee_script_hash_test', '''@equality_spec(Ty.Unit+Word256)CoreFunSem
          (inr(from_hash256(byteStringHash(txoScript o))),inr fee_empty_hash_word)'''),
        ('fee_spec_bit', '''match txoAmount o,txoAsset o with
          | Explicit _,Explicit _=>fee_script_hash_test o | _,_=>Bit.zero end'''),
        ('fee_spec_result', '''match nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))with
          | Some o=>inr(fee_spec_bit o)|None=>inl tt end'''),
    ]:
        definition(literal, name, expected)
    caller = coq / 'C/jet_elements_fee_flag_caller.v'
    definition(caller, 'processed_fee_result', '''match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
      | Some o => inr (if processed_fee_bit o then inr tt else inl tt) | None => inl tt end''')
    definition(caller, 'processed_fee_empty', 'match txoScript o with [] => true | _::_ => false end')
    definition(caller, 'processed_fee_bit', '''fee_classifier (processed_fee_empty o)
      (conf_prefix (clearPrf (txoAsset o))) (conf_prefix (clearPrf (txoAmount o)))''')
    definition(caller, 'processed_fee_rep', r'''Mem.load Mint8unsigned m b (ofs+241) = Some (Vint (fee_bool_int (processed_fee_empty o))) /\
      Mem.load Mint32 m b (ofs+32) = Some (Vint (conf_prefix (clearPrf (txoAsset o)))) /\
      Mem.load Mint32 m b (ofs+136) = Some (Vint (conf_prefix (clearPrf (txoAmount o))))''')
    definition(coq / 'C/jet_elements_fee_compare.v', 'fee_explicit_components',
               'match txoAsset o,txoAmount o with Explicit _,Explicit _=>Datatypes.true|_,_=>Datatypes.false end')
    compare = read(coq / 'C/jet_elements_fee_compare.v')
    statements = re.findall(r'Theorem elements_output_fee_implementation_comparison\s*:(.*?)\bProof\.', compare, re.S)
    expected = r'''application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
      (Ty.Sum Ty.Unit Bit)
      (indexed_ptr_rep(fun e=>sigTxOut(Elements.envTx e))processed_fee_rep 248 0 8 704)
      (fun a environment=>Some(processed_fee_result a environment)) /\
      forall a environment,
      (Some(processed_fee_result a environment)<>
       @elements_output_fee_spec(PrimitivePrimSem option_Monad_Zero)a environment <->
       exists o,nth_error(sigTxOut(Elements.envTx environment))(Z.to_nat(toZ a))=Some o /\
       fee_explicit_components o=Datatypes.true /\txoScript o<>[] /\byteStringHash(txoScript o)=byteStringHash []).'''
    if len(statements) != 1:
        raise ValueError('missing/ambiguous fee comparison')
    equal(statements[0], expected, 'whole C execution and exact comparison boundary')
    total = coq / 'C/jet_elements_total_fee_literal.v'
    for name, expected in [
        ('total_fee_literal_tail', '''case (injl (drop(drop(drop iden))))
          (injr (case (drop(drop(drop iden))) (drop(case (drop(drop iden))
           (((take(take iden)&&&injr(drop(take iden))) >>> equality_spec (Ty.Sum(Ty.Prod Bit Word256)Word256))
            &&&(take(drop iden)&&&drop(drop iden)) >>> case (drop(drop iden))
              (drop(case (drop iden) (Word.adder >>> drop iden))))))))'''),
        ('elements_total_fee_body', '''elements_comp
          (elements_pair (take(drop elements_output_fee_spec))
           (elements_pair (take(drop elements_output_amount_spec)) (take(take iden)&&&drop iden)))
          (elements_core(fun core=>@total_fee_literal_tail core))'''),
        ('total_fee_literal_program', '''(iden&&&(unit>>>Word.zero)) >>>
          for_while_program 5 body >>> copair iden iden'''),
        ('elements_total_fee_spec', 'total_fee_literal_program elements_total_fee_body'),
        ('total_fee_literal_zero', '@Word.zero 6 CoreFunSem tt'),
        ('total_fee_literal_step', '''match txoAsset o,txoAmount o with
          | Explicit asset,Explicit v=>if Bit.toBool(fee_script_hash_test o) then
           if Bit.toBool(@equality_spec Word256 CoreFunSem(key,from_hash256 asset)) then
            snd(@Word.adder 6 CoreFunSem(@fromZ (WordToZ 6)(Int64.unsigned v),acc)) else acc
           else acc | _,_=>acc end'''),
        ('total_fee_literal_result', '''fold_left(total_fee_literal_step key)
          (sigTxOut(Elements.envTx environment))total_fee_literal_zero'''),
    ]:
        definition(total, name, expected)
    return paths


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
    cbody('isFee', '''return output->emptyScript && EXPLICIT == output->asset.prefix && EXPLICIT == output->amt.prefix;''')
    cbody('simplicity_output_is_fee', '''uint_fast32_t i = simplicity_read32(&src);
      if (writeBit(dst, i < env->tx->numOutputs)) { writeBit(dst, isFee(&env->tx->output[i]));
      } else { skipBits(dst, 1); } return true;''')
    cbody('simplicity_total_fee', '''sha256_midstate assetid; readHash(&assetid, &src);
      simplicity_write64(dst, lookup_fee(&assetid, env->tx->feeOutputs, env->tx->numFees)); return true;''')
    paths.extend(check_fee(repo))
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.InputAmount', 'Elements.OutputAmount', 'Elements.CurrentAmount'],
             primitive_and_jet_codomain_distinguished=True, canonical_pair_routing_reviewed=True,
             explicit_word64_and_padding_reviewed=True, whole_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             fee_comparison_jet='Elements.OutputIsFee', fee_literal_and_comparison_reviewed=True,
             fee_empty_digest_converse_proved=False, fee_equivalence_or_reachable_divergence_proved=False,
             total_fee_literal_fold_reviewed=True, total_fee_table_correspondence_proved=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
