"""Selected Elements count-program/primitive observation review, not admission.

Only indexed lookup presence is reviewed for the two hash primitives. Hash
payload fidelity is intentionally not claimed; the any-payload C contracts
discharge that dependence formally. Other Elements primitive clauses remain
outside this review. Compilation and recursive kernel checking are separate.
"""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def between(text, first, last):
    if text.count(first) != 1 or text.count(last) != 1:
        raise ValueError('missing/ambiguous source boundary: ' + first)
    return text.split(first, 1)[1].split(last, 1)[0]


def check(repo, coq):
    helper = repo / 'Coq/check-secp-predicates-specification.py'
    parser = load('count_active_source_parser', helper)
    compact = parser.compact
    paths = [helper]
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if compact(actual) != compact(expected):
            raise ValueError('count source differs: ' + label)
    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)

    jets = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    transaction = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    parser.require(jets, 'import qualified Simplicity.Elements.Programs.Transaction.Lib as Prog', 'catalog module')
    parser.require(library, 'import qualified Simplicity.Elements.Programs.Transaction as Transaction', 'library module')
    program = transaction.split('l@Lib{..} = Lib {', 1)[1]
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    parser.require(hs, 'primPrefix = "Elements"', 'canonical primitive namespace')
    for fragment in ['primSem p a env = interpret p a', 'tx = envTx env',
                     'lookupInput = (sigTxIn tx !?) . fromIntegral',
                     'lookupOutput = (sigTxOut tx !?) . fromIntegral',
                     'cast (Just x) = Right x', 'cast Nothing = Left ()',
                     'atInput f = cast . fmap f . lookupInput . fromInteger . fromWord32',
                     'atOutput f = cast . fmap f . lookupOutput . fromInteger . fromWord32']:
        parser.require(hs, fragment, fragment)
    port = read(coq / 'C/jet_elements_prim.v')
    equal(parser.definition(port, 'primName'), '"Elements"', 'namespace')
    parser.require(port, 'Module Elements <: PrimitiveSig.', 'actual primitive module')
    parser.require(port, 'Module Export PrimitiveElements := PrimitiveModule Elements.', 'primitive algebra')
    sem = parser.definition(port, 'sem')
    before = sem.split('(match p in prim A B return A -> option B with', 1)[0]
    equal(before, '''let tx := envTx e in let ix := envIx e in
      let atInput {A : Ty} (f : sigTxInput -> A) (i : Word32) : option (tySem (S A)) :=
        Some (cast (option_map f (nth_error (sigTxIn tx) (Z.to_nat (toZ i))))) in
      let atOutput {A : Ty} (f : txOutput -> A) (i : Word32) : option (tySem (S A)) :=
        Some (cast (option_map f (nth_error (sigTxOut tx) (Z.to_nat (toZ i))))) in''', 'primitive lookup domain')
    if not compact(sem).endswith('end)a'):
        raise ValueError('primitive result application changed')
    cast = re.search(r'Let cast\b.*?:=(.*?)\.\s*\n', port, re.S)
    if not cast:
        raise ValueError('missing primitive option-to-sum embedding')
    equal(cast[1], 'match x with | Some a => inr a | None => inl tt end', 'primitive lookup verdict')
    root = read(coq / 'C/jet_elements_count_local.v')
    for constructor, accessor, nxt, prim, prim_next, at, field, offset in [
        ('NumInputs', 'numInputs', 'numOutputs', 'InputScriptHash', 'InputSequence', 'atInput', 'sigTxIn', 696),
        ('NumOutputs', 'numOutputs', 'outputAmount', 'OutputScriptHash', 'OutputNullDatum', 'atOutput', 'sigTxOut', 704),
    ]:
        suffix = 'num_inputs' if constructor == 'NumInputs' else 'num_outputs'
        parser.require(jets, constructor + ' :: TransactionJet () Word32', 'jet type')
        dispatch = re.findall(r'(?m)^specificationTransaction ' + constructor + r'\s*=([^\n]*)$', jets)
        if len(dispatch) != 1:
            raise ValueError('missing/duplicate catalog dispatch')
        equal(dispatch[0], 'Prog.' + accessor, 'catalog dispatch')
        parser.require(library, accessor + ' = Transaction.' + accessor + ' Transaction.lib', 'library binding')
        parser.exact_program(program, accessor, nxt, 'firstFail word32 (primitive ' + prim + ')')
        parser.require(hs, prim + ' :: Prim Word32 (S Word256)', 'indexed primitive type')
        name = 'inputScriptHash' if prim == 'InputScriptHash' else 'outputScriptHash'
        parser.require(hs, 'primName ' + prim + ' = "' + name + '"', 'primitive identity')
        parser.require(port, '| ' + prim + ' : prim Word32 (S Word256)', 'Coq primitive type')
        identities = re.findall(r'(?m)^\s*\| ' + prim + r'\s*=>\s*"([^"\n]*)"\s*$', port)
        if identities != [name]:
            raise ValueError('Coq primitive identity changed')
        interpretation = re.findall(r'(?m)^  interpret ' + prim + r'\s*=([^\n]*)$', hs)
        expression = ('encodeHash . bslHash . utxoScript . sigTxiTxo' if prim == 'InputScriptHash' else
                      'encodeHash . bslHash . txoScript')
        if len(interpretation) != 1:
            raise ValueError('missing/duplicate canonical primitive clause')
        equal(interpretation[0], 'return . (' + at + ' $ ' + expression + ')', 'canonical lookup observation')
        clause = re.findall(r'(?ms)^\s*\| ' + prim + r'\s*=>(.*?)(?=^\s*\| ' + prim_next + r'\s*=>)', sem)
        if len(clause) != 1 or not re.fullmatch(at + r'\s*\(fun\s+\w+\s*=>.+\)', clause[0].strip(), re.S):
            raise ValueError('indexed primitive does not directly map a total payload through lookup')
        definition(coq / 'C/jet_elements_count_canonical.v', 'elements_transaction_' + suffix + '_spec',
                   'first_fail_program 5 (Primitive.Combinators.prim Elements.' + prim + ')')
        wanted = ('application_jet_local_spec f_simplicity_' + suffix + ' elements_ge Elements.env Ty.Unit Word32 '
                  'elements_' + suffix + '_env_rep (fun a environment => @elements_transaction_' + suffix +
                  '_spec (PrimitivePrimSem option_Monad_Zero) a environment).')
        statement = re.findall(r'\bTheorem elements_' + suffix + r'_local_spec\s*:(.*?)\bProof\s*\.', root, re.S)
        if len(statement) != 1:
            raise ValueError('missing/duplicate C contract')
        equal(statement[0], wanted, 'actual C function/environment/specification/whole local contract')
        equal(parser.definition(root, 'elements_' + suffix + '_env_rep'),
              'elements_count_env_rep ' + str(offset) +
              ' (fun environment => Z.of_nat (length (' + field + ' (Elements.envTx environment))))', 'count field')
    equal(parser.definition(root, 'elements_count_env_rep'), r'''exists be ebase bt txbase value,
      env = Vptr be (Ptrofs.repr ebase) /\
      0 <= ebase <= Ptrofs.max_unsigned /\ 0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
      Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
      Mem.load Mint64 m bt (txbase + delta) = Some (Vlong value) /\
      Int64.unsigned value = count environment''', 'initial physical/logical boundary')
    definition(coq / 'C/jet_firstFail_spec.v', 'first_fail_body',
               'take (drop ((op &&& iden) >>> case (injl (I H)) (injr unit)))')
    definition(coq / 'C/jet_firstFail_spec.v', 'first_fail_program',
               '(unit &&& unit) >>> for_while_program n (first_fail_body n op) >>> (iden &&& unit) >>> assertl (O H) assertion_cmr_fail0')
    word = read(repo / 'Haskell/Core/Simplicity/Programs/Word.hs')
    equal(between(word, 'firstFail w op =', 'data ConstWord'),
          '(unit &&& unit) >>> forWhile w (take (drop (op &&& iden >>> match (injl ih) (injr unit)))) '
          '>>> iden &&& unit >>> assertl (take iden) cmrFail0', 'literal firstFail')
    equal(between(word, 'forWhile SingleV body =', 'firstFail ::'),
          '(((oh &&& false) &&& ih) >>> monobody) &&& oh >>> match (injl oh) (((ih &&& true) &&& oh) >>> monobody) '
          'where monobody = body forWhile (DoubleV n) body = forWhile n (forWhile n ((oooh &&& (ooih &&& oih)) &&& ih >>> body))',
          'literal forWhile recursion')
    definition(coq / 'C/jet_forWhile_spec.v', 'for_while_program', '''
      match n as k return alg ((C * Word k) * A) (B + A) -> alg (C * A) (B + A) with
      | 0 => fun body => ((((O H &&& Bit.false) &&& I H) >>> body) &&& O H) >>>
          case (injl (O H)) (((I H &&& Bit.true) &&& O H) >>> body)
      | S k => fun body => for_while_program k (for_while_program k
          (((O O O H &&& (O O I H &&& O I H)) &&& I H) >>> body)) end body''')
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    for fragment in ['type Vector1 x = x', 'vector1 = SingleV', 'word32 = vector32',
                     'type Word32 = Vector32 Bit']:
        parser.require(words, fragment, '32-bit word carrier')
    for size, half in [(2, 1), (4, 2), (8, 4), (16, 8), (32, 16)]:
        parser.require(words, 'vector' + str(size) + ' = DoubleV vector' + str(half), 'word32 depth')
    definition(coq / 'C/jet_assertion_spec.v', 'assertion_hash0', '''Simplicity.Digest.Hash256
      [Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero; Int.zero] eq_refl''')
    definition(coq / 'C/jet_assertion_spec.v', 'assertion_cmr_fail0', '''
      @Alg.Assertion.Combinators.fail Ty.Unit Ty.Unit
      Simplicity.MerkleRoot.CommitmentRoot_Assertion_alg (assertion_hash0, assertion_hash0)''')
    merkle = read(repo / 'Haskell/Core/Simplicity/MerkleRoot/Impl.hs')
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    parser.require(merkle, 'cmrFail0 = commitmentRoot (fail0 :: CommitmentRoot () ())', 'assertion branch root')
    parser.require(core, 'fail0 = fail (hash0, hash0)', 'literal fail root payload')
    raw = read(repo / 'C/include/simplicity/elements/env.h')
    raw = re.sub(r'/\*.*?\*/|//[^\n]*', '', raw, flags=re.S)
    record = between(raw, 'typedef struct rawElementsTransaction {', '} rawElementsTransaction;')
    for name in ['numInputs', 'numOutputs']:
        if len(re.findall(r'(?m)^\s*uint32_t ' + name + r';\s*$', record)) != 1:
            raise ValueError('C raw count domain changed: ' + name)
    parser.require(port, 'sigTxInBounds : (0 < Zlength sigTxIn < Int.modulus)%Z', 'bounded input domain')
    parser.require(port, 'sigTxOutBounds : (0 <= Zlength sigTxOut < Int.modulus)%Z', 'bounded output domain')
    return {'scope': 'two count jets; literal programs and indexed lookup presence only',
            'hash_payload_fidelity_reviewed': False, 'other_primitive_semantics_reviewed': False,
            'kernel_checked_by_this_tool': False, 'AST_checked_by_this_tool': False,
            'normal_registration': False, 'coverage_added': 0,
            'hashes': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}}


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--repo', type=Path, required=True); p.add_argument('--coq', type=Path, required=True)
    args = p.parse_args(); import json; print(json.dumps(check(args.repo, args.coq), indent=2))
