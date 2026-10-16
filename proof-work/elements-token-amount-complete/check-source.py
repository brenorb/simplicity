"""Canonical token-amount branches and exact whole-C contracts; not acceptance."""
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
    prior = load('token_prior_source', HERE.parent / 'elements-issuance-amount-literal/check-source.py')
    r = prior.check(repo)
    p = load('token_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('token source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous token clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous token definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous token contract: ' + name)
        equal(found[0], expected, name)

    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    line(hs, 'issuanceTokenAmount', 'either newIssuanceTokenAmount (const (Amount (Explicit 0)))')
    p.require(hs, 'IssuanceTokenAmount :: Prim Word32 (S (S (Conf Word64)))', 'primitive type')
    line(hs, 'primName IssuanceTokenAmount', '"issuanceTokenAmount"')
    found = re.findall(r'(?ms)^\s*interpret IssuanceTokenAmount\s*=(.*?)(?=^\s*interpret )', hs)
    if len(found) != 1:
        raise ValueError('ambiguous token interpretation')
    equal(found[0], 'return . (atInput $ cast . fmap (encodeAmount . clearAmountPrf . issuanceTokenAmount) . sigTxiIssuance)', 'optional token routing')
    p.require(catalog, 'IssuanceTokenAmount :: TransactionJet Word32 (S (S (Conf Word64)))', 'indexed jet type')
    p.require(catalog, 'CurrentIssuanceTokenAmount :: TransactionJet () (S (Conf Word64))', 'current jet type')
    line(catalog, 'specificationTransaction IssuanceTokenAmount', 'primitive Prim.IssuanceTokenAmount')
    line(catalog, 'specificationTransaction CurrentIssuanceTokenAmount', 'Prog.currentIssuanceTokenAmount')
    line(read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs'), 'currentIssuanceTokenAmount',
         'Transaction.currentIssuanceTokenAmount Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous transaction library')
    line(program.split('lib = l', 1)[1], ', currentIssuanceTokenAmount',
         'primitive CurrentIndex >>> assert (primitive IssuanceTokenAmount)')
    port = coq / 'C/jet_elements_prim.v'
    definition(port, 'issuanceTokenAmount', 'match i with | inl new => newIssuanceTokenAmount new | inr _ => Explicit Int64.zero end')
    p.require(read(port), '| IssuanceTokenAmount : prim Word32 (S (S (Conf Word64)))', 'Coq primitive type')
    sem = p.definition(read(port), 'sem')
    if sem.count('| IssuanceTokenAmount =>') != 1 or sem.count('| IssuanceAssetProof =>') != 1:
        raise ValueError('ambiguous Coq token interpretation')
    equal(sem.split('| IssuanceTokenAmount =>', 1)[1].split('| IssuanceAssetProof =>', 1)[0],
          'atInput (fun txi => cast (option_map (fun i => encodeAmount (clearPrf (issuanceTokenAmount i))) (sigTxiIssuance txi)))', 'Coq token routing')
    select = coq / 'C/jet_elements_token_select.v'
    helper = coq / 'C/jet_elements_token_amount_exec.v'
    old = coq / 'C/jet_elements_token_amount_jets.v'
    literal = coq / 'C/jet_elements_token_amount_literal.v'
    definition(select, 'token_selected_amount', 'match i with inl new => clearPrf (newIssuanceTokenAmount new) | inr _ => Explicit Int64.zero end')
    definition(helper, 'token_issuance_rep', r'''Mem.load Mint32 m bi (ibase + 272) = Some (Vint (issuance_tag o)) /\
      forall new, o = Some (inl new) -> amount_rep m bi (ibase + 32) (clearPrf (newIssuanceTokenAmount new))''')
    definition(old, 'issuance_token_rep', 'token_issuance_rep m b ofs (sigTxiIssuance txi)')
    definition(old, 'issuance_token_value', 'match sigTxiIssuance txi with Some i => inr (encode_amount (token_selected_amount i)) | None => inl tt end')
    definition(old, 'elements_issuance_token_amount_spec', 'Primitive.Combinators.prim Elements.IssuanceTokenAmount')
    definition(old, 'elements_current_issuance_token_amount_spec', 'elements_current_spec (@elements_issuance_token_amount_spec alg)')
    p.require(read(literal), 'Local Notation ConfAmount := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64).', 'literal amount width')
    definition(literal, 'issuance_token_amount_literal', '''match sigTxiIssuance txi with
      | None => inl tt
      | Some (inl new) => inr (encode_amount_literal (clearPrf (newIssuanceTokenAmount new)))
      | Some (inr _) => inr (encode_amount_literal (Explicit Int64.zero)) end''')
    definition(literal, 'elements_issuance_token_amount_literal_spec', '''@word_indexed_value_literal sigTxInput (Ty.Sum Ty.Unit ConfAmount) 5
      issuance_token_amount_literal (sigTxIn (Elements.envTx environment)) a''')
    definition(literal, 'elements_current_issuance_token_amount_literal_spec',
               'elements_current_literal_result elements_issuance_token_amount_literal_spec')
    for iscur in [False, True]:
        suffix = ('current_' if iscur else '') + 'issuance_token_amount'
        rep = ('''(current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx issuance_token_rep 544 256 0 696) ''' if iscur else
               '''(indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_token_rep 544 256 0 696) ''')
        prefix = ': application_jet_local_spec_sep f_simplicity_' + suffix + ' elements_ge Elements.env '
        prefix += 'Ty.Unit (Ty.Sum Ty.Unit ' if iscur else 'Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit '
        for lit, path in [(False, old), (True, literal)]:
            name = 'elements_' + suffix + ('_literal' if lit else '')
            ty = ('ConfAmount' if lit else '(ConfTy Word64)') + (') ' if iscur else ')) ')
            spec = name + '_spec.' if lit else '(fun a environment => @elements_' + suffix + '_spec (PrimitivePrimSem option_Monad_Zero) a environment).'
            statement(path, name + '_local_spec', prefix + ty + rep + spec)

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    def cbody(name, expected):
        found = list(re.finditer(r'\b(?:bool|void)\s+' + re.escape(name) + r'\s*\([^)]*\)\s*\{', c))
        if len(found) != 1:
            raise ValueError('missing/ambiguous token C body')
        start, end, depth = found[0].end(), found[0].end(), 1
        while end < len(c) and depth:
            depth += (c[end] == '{') - (c[end] == '}')
            end += 1
        if depth:
            raise ValueError('unterminated token C body')
        equal(c[start:end-1], expected, name)
    cbody('issuanceTokenAmt', '''if (writeBit(dst, NO_ISSUANCE != issuance->type)) {
      amt(dst, NEW_ISSUANCE == issuance->type ? &issuance->tokenAmt : &(confAmount){ .prefix = EXPLICIT, .explicit = 0});
      } else { skipBits(dst, 258); }''')
    cbody('simplicity_issuance_token_amount', '''uint_fast32_t i = simplicity_read32(&src);
      if (writeBit(dst, i < env->tx->numInputs)) { issuanceTokenAmt(dst, &env->tx->input[i].issuance);
      } else { skipBits(dst, 259); } return true;''')
    cbody('simplicity_current_issuance_token_amount', '''(void) src; if (env->tx->numInputs <= env->ix) return false;
      issuanceTokenAmt(dst, &env->tx->input[env->ix].issuance); return true;''')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.pop('token_amount_proved', None)
    r.update(selected_jets=['Elements.IssuanceTokenAmount', 'Elements.CurrentIssuanceTokenAmount'],
             reissuance_explicit_zero_reviewed=True, whole_c_token_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
