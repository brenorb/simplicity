"""Canonical optional issuance amount selectors and original whole-C contracts.

Reuse the reviewed Word64 encoder/index/current guards. No caller construction,
host-library equivalence, token-amount proof or normal acceptance is claimed.
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
    prior = load('issuance_amount_shared_source', HERE.parent / 'elements-amount-literal/check-source.py')
    r = prior.check(repo)
    p = load('issuance_amount_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('issuance amount source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance amount clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance amount definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole issuance amount contract: ' + name)
        equal(found[0], expected, name)

    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    line(hs, 'issuanceAmount', 'either newIssuanceAmount reissuanceAmount')
    p.require(hs, 'IssuanceAssetAmount :: Prim Word32 (S (S (Conf Word64)))', 'indexed primitive type')
    line(hs, 'primName IssuanceAssetAmount', '"issuanceAssetAmount"')
    found = re.findall(r'(?ms)^\s*interpret IssuanceAssetAmount\s*=(.*?)(?=^\s*interpret )', hs)
    if len(found) != 1:
        raise ValueError('missing/ambiguous issuance amount interpretation')
    equal(found[0], 'return . (atInput $ cast . fmap (encodeAmount . clearAmountPrf . issuanceAmount) . sigTxiIssuance)',
          'optional issuance interpretation')
    p.require(catalog, 'IssuanceAssetAmount :: TransactionJet Word32 (S (S (Conf Word64)))', 'indexed jet type')
    p.require(catalog, 'CurrentIssuanceAssetAmount :: TransactionJet () (S (Conf Word64))', 'current jet type')
    line(catalog, 'specificationTransaction IssuanceAssetAmount', 'primitive Prim.IssuanceAssetAmount')
    line(catalog, 'specificationTransaction CurrentIssuanceAssetAmount', 'Prog.currentIssuanceAssetAmount')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    line(library, 'currentIssuanceAssetAmount', 'Transaction.currentIssuanceAssetAmount Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous transaction program library')
    line(program.split('lib = l', 1)[1], ', currentIssuanceAssetAmount',
         'primitive CurrentIndex >>> assert (primitive IssuanceAssetAmount)')

    port = coq / 'C/jet_elements_prim.v'
    definition(port, 'issuanceAmount', 'match i with | inl new => newIssuanceAmount new | inr re => reissuanceAmount re end')
    sem = p.definition(read(port), 'sem')
    p.require(read(port), '| IssuanceAssetAmount : prim Word32 (S (S (Conf Word64)))', 'Coq primitive type')
    if sem.count('| IssuanceAssetAmount =>') != 1 or sem.count('| IssuanceTokenAmount =>') != 1:
        raise ValueError('ambiguous Coq issuance amount primitive')
    equal(sem.split('| IssuanceAssetAmount =>', 1)[1].split('| IssuanceTokenAmount =>', 1)[0],
          'atInput (fun txi => cast (option_map (fun i => encodeAmount (clearPrf (issuanceAmount i))) (sigTxiIssuance txi)))',
          'Coq optional issuance semantics')
    old = coq / 'C/jet_elements_issuance_amount_jets.v'
    current = coq / 'C/jet_elements_current_input_jets.v'
    local = coq / 'C/jet_elements_issuance_amount_literal.v'
    definition(old, 'issuance_amount', 'match i with inl new => newIssuanceAmount new | inr re => reissuanceAmount re end')
    definition(old, 'issuance_amount_rep', r'''Mem.load Mint32 m b (ofs + 272) = Some (Vint (issuance_tag (sigTxiIssuance txi))) /\
      forall i, sigTxiIssuance txi = Some i -> amount_rep m b (ofs + 232) (clearPrf (issuance_amount i))''')
    definition(old, 'issuance_amount_result', '''match nth_error elems (Z.to_nat (toZ a)) with
      | Some txi => inr (match sigTxiIssuance txi with
        | Some i => inr (encode_amount (clearPrf (issuance_amount i))) | None => inl tt end)
      | None => inl tt end''')
    definition(old, 'elements_issuance_asset_amount_spec', 'Primitive.Combinators.prim Elements.IssuanceAssetAmount')
    definition(current, 'elements_current_issuance_asset_amount_spec', 'elements_current_spec (@elements_issuance_asset_amount_spec alg)')
    p.require(read(local), 'Local Notation ConfAmount := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64).', 'amount widths')
    definition(local, 'issuance_asset_amount_literal', '''match sigTxiIssuance txi with
      | None => inl tt
      | Some (inl new) => inr (encode_amount_literal (clearPrf (newIssuanceAmount new)))
      | Some (inr re) => inr (encode_amount_literal (clearPrf (reissuanceAmount re))) end''')
    definition(local, 'elements_issuance_asset_amount_literal_spec', '''@word_indexed_value_literal sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
      issuance_asset_amount_literal (sigTxIn (Elements.envTx environment)) a''')
    definition(local, 'elements_current_issuance_asset_amount_literal_spec',
               'elements_current_literal_result elements_issuance_asset_amount_literal_spec')
    for iscur in [False, True]:
        suffix = ('current_' if iscur else '') + 'issuance_asset_amount'
        rep = ('''(current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx issuance_amount_rep 544 256 0 696) ''' if iscur else
               '''(indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_amount_rep 544 256 0 696) ''')
        prefix = ': application_jet_local_spec_sep f_simplicity_' + suffix + ' elements_ge Elements.env '
        prefix += 'Ty.Unit (Ty.Sum Ty.Unit ' if iscur else 'Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit '
        for literal, path in [(False, current if iscur else old), (True, local)]:
            name = 'elements_' + suffix + ('_literal' if literal else '')
            ty = ('ConfAmount' if literal else '(ConfTy Word64)') + (') ' if iscur else ')) ')
            spec = name + '_spec.' if literal else '(fun a environment => @elements_' + suffix + '_spec (PrimitivePrimSem option_Monad_Zero) a environment).'
            statement(path, name + '_local_spec', prefix + ty + rep + spec)

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    def cbody(name, expected):
        found = list(re.finditer(r'\b(?:bool|void)\s+' + re.escape(name) + r'\s*\([^)]*\)\s*\{', c))
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance amount C function')
        start, end, depth = found[0].end(), found[0].end(), 1
        while end < len(c) and depth:
            depth += (c[end] == '{') - (c[end] == '}')
            end += 1
        if depth:
            raise ValueError('unterminated issuance amount C function')
        equal(c[start:end-1], expected, name)
    cbody('issuanceAssetAmt', '''if (writeBit(dst, NO_ISSUANCE != issuance->type)) {
      amt(dst, &issuance->assetAmt); } else { skipBits(dst, 258); }''')
    cbody('simplicity_issuance_asset_amount', '''uint_fast32_t i = simplicity_read32(&src);
      if (writeBit(dst, i < env->tx->numInputs)) { issuanceAssetAmt(dst, &env->tx->input[i].issuance);
      } else { skipBits(dst, 259); } return true;''')
    cbody('simplicity_current_issuance_asset_amount', '''(void) src; if (env->tx->numInputs <= env->ix) return false;
      issuanceAssetAmt(dst, &env->tx->input[env->ix].issuance); return true;''')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.IssuanceAssetAmount', 'Elements.CurrentIssuanceAssetAmount'],
             optional_issuance_branches_reviewed=True, whole_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             token_amount_proved=False, normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
