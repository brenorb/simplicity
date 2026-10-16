"""Asset getter source/representation correspondence, not field arithmetic.

fe_repr reads fe_pack. The Coq point hash models that serialized packed word;
this guard does not claim arbitrary words are valid FE values or prove a host
lens/compiler theorem. Whole C contracts and existing preconditions stay exact.
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
    prior = load('asset_shared_nonce_source', HERE.parent / 'elements-output-nonce/check-source.py')
    r = prior.check(repo)
    p = load('asset_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('asset source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous asset clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous asset definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole asset contract: ' + name)
        equal(found[0], expected, name)

    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for tag, name, route in [('InputAsset', 'inputAsset', 'utxoAsset . sigTxiTxo'),
                             ('OutputAsset', 'outputAsset', 'clearAssetPrf . txoAsset')]:
        p.require(catalog, tag + ' :: TransactionJet Word32 (S (Conf Word256))', 'catalog type')
        line(catalog, 'specificationTransaction ' + tag, 'primitive Prim.' + tag)
        p.require(hs, tag + ' :: Prim Word32 (S (Conf Word256))', 'primitive type')
        line(hs, 'primName ' + tag, '"' + name + '"')
        line(hs, 'interpret ' + tag, 'return . (at' + ('Input' if tag == 'InputAsset' else 'Output') +
             ' $ encodeAsset . ' + route + ')')
    p.require(catalog, 'CurrentAsset :: TransactionJet () (Conf Word256)', 'current asset type')
    line(catalog, 'specificationTransaction CurrentAsset', 'Prog.currentAsset')
    line(hs, 'encodeConfidential enc (Explicit a)', 'Right (enc a)')
    line(hs, 'encodeConfidential enc (Confidential (Point by x) ())',
         'Left (toBit by, toWord256 . Schnorr.fe_repr $ x)')
    line(hs, 'encodeAsset', 'encodeConfidential encodeHash . view (under asset)')
    p.require(hs, 'import qualified Simplicity.LibSecp256k1.Spec as Schnorr', 'fe_repr import origin')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    p.require(data, 'data Confidential prf a = Explicit a | Confidential Point prf', 'confidential sum')
    p.require(data, 'newtype AssetWith prf = Asset (Confidential prf Hash256)', 'asset newtype')
    p.require(data, 'type Asset = AssetWith ()', 'unit proof carrier')
    line(data, 'prf_ f (Confidential pt prf)', 'Confidential pt <$> f prf')
    line(data, 'prf_ f (Explicit x)', 'pure (Explicit x)')
    line(data, 'clearAssetPrf x', 'x & under asset . prf_ .~ ()')
    if data.count('\nasset =') != 1 or data.count('clearAssetPrf ::') != 1:
        raise ValueError('ambiguous asset lens adapter')
    equal(data.split('\nasset =', 1)[1].split('clearAssetPrf ::', 1)[0],
          'adapter to fro where to (Asset x) = x fro x = (Asset x)', 'asset adapter')
    line(data, 'putFE', 'put . fe_pack')
    spec = read(repo / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs')
    p.require(spec, 'data FE = FE { fe_pack :: Word256 }', 'packed field carrier')
    p.require(spec, 'data Point = Point Bool FE', 'parity and packed field carrier')
    line(spec, 'fe_repr', 'toInteger . fe_pack')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    line(library, 'currentAsset', 'Transaction.currentAsset Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous current asset library')
    found = re.findall(r'(?m)^\s*, currentAsset\s*=([^\n]*)$', program.split('lib = l', 1)[1])
    if len(found) != 1:
        raise ValueError('missing/ambiguous current asset program')
    equal(found[0], 'primitive CurrentIndex >>> assert (primitive InputAsset)', 'current asset assertion')
    line(hs, 'cond', 'fromIntegral ix < Vector.length (sigTxIn tx)')

    port = coq / 'C/jet_elements_prim.v'
    code = read(port)
    p.require(code, 'Record point : Set := Point { pointOdd : bool; pointX : hash256 }.', 'packed word port')
    p.require(code, 'envIxBounded : (envIx < length (sigTxIn envTx))%nat', 'valid current input')
    definition(port, 'clearPrf', 'match c with | Explicit a => Explicit a | Confidential pt _ => Confidential pt tt end')
    sem = p.definition(code, 'sem')
    for tag, following, expr in [
        ('InputAsset', 'InputAmount', 'atInput (fun txi => encodeAsset (utxoAsset (sigTxiTxo txi)))'),
        ('OutputAsset', 'OutputAmount', 'atOutput (fun txo => encodeAsset (clearPrf (txoAsset txo)))')]:
        p.require(code, '| ' + tag + ' : prim Word32 (S (Conf Word256))', 'Coq primitive type')
        if sem.count('| ' + tag + ' =>') != 1 or sem.count('| ' + following + ' =>') != 1:
            raise ValueError('ambiguous asset primitive')
        equal(sem.split('| ' + tag + ' =>', 1)[1].split('| ' + following + ' =>', 1)[0], expr, tag)

    literal = coq / 'C/jet_elements_asset_literal.v'
    p.require(read(literal), 'Local Notation ConfLiteral a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).',
              'full confidential sum shape')
    p.require(read(literal), 'Local Notation AssetConf := (ConfLiteral Word256).', 'asset payload width')
    definition(literal, 'packed_fe_integer_literal', '''haskell_word256_integer
      (haskell_be256_run (hash256_to_bytelist packed) (haskell_word256_from_integer 0))''')
    definition(literal, 'encode_confidential_literal', '''match c with
      | Explicit x => inr (enc x)
      | Confidential (Point odd packed) _ =>
        inl ((if odd then inr tt else inl tt), haskell_to_word 8 (packed_fe_integer_literal packed)) end''')
    definition(literal, 'encode_asset_literal', '''encode_confidential_literal
      (fun h => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) a''')
    definition(literal, 'elements_input_asset_literal_spec', '''word_indexed_value_literal 5
      (fun txi => encode_asset_literal (utxoAsset (sigTxiTxo txi))) (sigTxIn (Elements.envTx environment)) a''')
    definition(literal, 'elements_output_asset_literal_spec', '''word_indexed_value_literal 5
      (fun txo => encode_asset_literal (clearPrf (txoAsset txo))) (sigTxOut (Elements.envTx environment)) a''')
    definition(literal, 'elements_current_asset_literal_spec', 'elements_current_literal_result elements_input_asset_literal_spec')
    old = coq / 'C/jet_elements_asset_jets.v'
    definition(old, 'asset_words', 'hash256_reg (match a with Explicit h => h | Confidential (Point _ x) _ => x end)')
    definition(old, 'asset_rep', r'''uint32_array_at m b ofs (asset_words a) /\
      Mem.load Mint32 m b (ofs + 32) = Some (Vint (conf_prefix a))''')
    definition(old, 'encode_asset', '''match a with | Explicit h => inr (from_hash256 h)
      | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x) end''')
    current = coq / 'C/jet_elements_current_input_jets.v'
    for suffix, path in [('input', old), ('output', old), ('current', current)]:
        definition(path, 'elements_' + suffix + '_asset_spec',
            'elements_current_spec (@elements_input_asset_spec alg)' if suffix == 'current' else
            'Primitive.Combinators.prim Elements.' + suffix.capitalize() + 'Asset')
        isout, iscur = suffix == 'output', suffix == 'current'
        rep = ('''(current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx
          (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) 544 168 0 696) ''' if iscur else
          '''(indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
          (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo))) 248 0 8 704) ''' if isout else
          '''(indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
          (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) 544 168 0 696) ''')
        prefix = ': application_jet_local_spec_sep f_simplicity_' + suffix + '_asset elements_ge Elements.env '
        oldty = 'Ty.Unit (ConfTy Word256) ' if iscur else 'Word32 (Ty.Sum Ty.Unit (ConfTy Word256)) '
        newty = 'Ty.Unit AssetConf ' if iscur else 'Word32 (Ty.Sum Ty.Unit AssetConf) '
        statement(path, 'elements_' + suffix + '_asset_local_spec', prefix + oldty + rep +
            '(fun a environment => @elements_' + suffix + '_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment).')
        statement(literal, 'elements_' + suffix + '_asset_literal_local_spec', prefix + newty + rep +
            'elements_' + suffix + '_asset_literal_spec.')

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    def cbody(name, expected):
        found = list(re.finditer(r'\b(?:bool|void)\s+' + re.escape(name) + r'\s*\([^)]*\)\s*\{', c))
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual asset C function')
        start, end, depth = found[0].end(), found[0].end(), 1
        while end < len(c) and depth:
            depth += (c[end] == '{') - (c[end] == '}')
            end += 1
        if depth:
            raise ValueError('unterminated C function')
        equal(c[start:end-1], expected, name)
    cbody('asset', '''if (writeBit(dst, EXPLICIT == asset->prefix)) { skipBits(dst, 1); }
      else { writeBit(dst, ODD_Y == asset->prefix); } writeHash(dst, &asset->data);''')
    for suffix, count, address in [('input', 'numInputs', 'input[i].txo.asset'),
                                    ('output', 'numOutputs', 'output[i].asset')]:
        cbody('simplicity_' + suffix + '_asset', '''uint_fast32_t i = simplicity_read32(&src);
          if (writeBit(dst, i < env->tx->''' + count + ''')) { asset(dst, &env->tx->''' + address + '''); }
          else { skipBits(dst, 258); } return true;''')
    cbody('simplicity_current_asset', '''(void) src; if (env->tx->numInputs <= env->ix) return false;
      asset(dst, &env->tx->input[env->ix].txo.asset); return true;''')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r['shared_nonce_native_word_reviewed'] = r.pop('native_word_not_field_element')
    r.update(selected_jets=['Elements.InputAsset', 'Elements.OutputAsset', 'Elements.CurrentAsset'],
             packed_field_projection_reviewed=True, field_arithmetic_proved=False,
             arbitrary_word_is_valid_field_element_claimed=False, whole_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
