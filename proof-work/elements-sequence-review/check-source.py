"""Selected InputSequence program, primitive and literal word-conversion port.

This is a source correspondence guard, not compilation, a kernel check or
normal admission. It deliberately makes no claim about the other primitives.
"""
import argparse
import hashlib
import importlib.util
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def check(repo, coq, literal):
    path = coq / 'check-secp-predicates-specification.py'
    spec = importlib.util.spec_from_file_location('sequence_source_parser', path)
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    paths = [path]
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('sequence source differs: ' + label)
    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)
    def between(text, start, end):
        if text.count(start) != 1 or text.count(end) != 1:
            raise ValueError('ambiguous sequence source boundary')
        return text.split(start, 1)[1].split(end, 1)[0]
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for fragment in ['InputSequence :: TransactionJet Word32 (S Word32)',
                     'import qualified Simplicity.Elements.Primitive as Prim']:
        parser.require(catalog, fragment, fragment)
    matches = re.findall(r'(?m)^specificationTransaction InputSequence\s*=([^\n]*)$', catalog)
    if len(matches) != 1:
        raise ValueError('missing/duplicate sequence dispatch')
    equal(matches[0], 'primitive Prim.InputSequence', 'canonical primitive jet')
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    for fragment in ['primPrefix = "Elements"', 'InputSequence :: Prim Word32 (S Word32)',
                     'primName InputSequence = "inputSequence"', 'primSem p a env = interpret p a',
                     'tx = envTx env', 'lookupInput = (sigTxIn tx !?) . fromIntegral',
                     'cast (Just x) = Right x', 'cast Nothing = Left ()',
                     'atInput f = cast . fmap f . lookupInput . fromInteger . fromWord32']:
        parser.require(hs, fragment, fragment)
    matches = re.findall(r'(?m)^  interpret InputSequence\s*=([^\n]*)$', hs)
    if len(matches) != 1:
        raise ValueError('missing/duplicate sequence interpretation')
    equal(matches[0], 'return . (atInput $ toWord32 . toInteger . sigTxiSequence)', 'primitive result')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    parser.require(data, 'import Data.Word (Word64, Word32, Word16, Word8)', 'unsigned source carrier')
    parser.require(data, 'sigTxiSequence :: Word32', 'bounded source field')
    port = read(coq / 'C/jet_elements_prim.v')
    parser.require(port, '; sigTxiSequence : int', 'CompCert int carrier')
    parser.require(port, '| InputSequence : prim Word32 (S Word32)', 'primitive type')
    parser.require(port, '| InputSequence => "inputSequence"', 'primitive name')
    equal(parser.definition(port, 'primName'), '"Elements"', 'primitive namespace')
    sem = parser.definition(port, 'sem')
    equal(between(sem, '| InputSequence =>', '| InputAnnexHash =>'),
          'atInput (fun txi => fromZ (Int.unsigned (sigTxiSequence txi)))', 'Coq primitive clause')
    prelude = sem.split('(match p in prim A B return A -> option B with', 1)[0]
    cast = re.search(r'Let cast\b.*?:=(.*?)\.\s*\n', port, re.S)
    if cast is None:
        raise ValueError('missing option-to-sum embedding')
    equal(cast[1], 'match x with | Some a => inr a | None => inl tt end', 'Coq lookup verdict')
    equal(prelude, '''let tx := envTx e in let ix := envIx e in
      let atInput {A : Ty} (f : sigTxInput -> A) (i : Word32) : option (tySem (S A)) :=
        Some (cast (option_map f (nth_error (sigTxIn tx) (Z.to_nat (toZ i))))) in
      let atOutput {A : Ty} (f : txOutput -> A) (i : Word32) : option (tySem (S A)) :=
        Some (cast (option_map f (nth_error (sigTxOut tx) (Z.to_nat (toZ i))))) in''', 'lookup/presence')
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    equal(between(words, 'toWord w i =', 'fromWord1 ::'), '''
      evalState (go w) i where go :: Word a -> State Integer a
      go SingleV = do i <- get put (i `div` 2) return $ toBit (odd i)
      go (DoubleV w) = do b <- go w a <- go w return (a, b)''', 'literal state traversal')
    equal(between(words, 'fromWord =', 'fromInt ::'), '''
      fromWordRec 0 fromWordRec :: Integer -> Word a -> a -> Integer
      fromWordRec i SingleV (Left ()) = 2 * i
      fromWordRec i SingleV (Right ()) = 2 * i + 1
      fromWordRec i (DoubleV w) (hi, lo) = fromWordRec (fromWordRec i w hi) w lo''', 'literal input decoder')
    for fragment in ['toWord32 = toWord word32', 'fromWord32 = fromWord word32',
                     'word32 = vector32', 'vector1 = SingleV', 'type Vector1 x = x',
                     'type Vector2 x = (x,x)', 'type Word32 = Vector32 Bit']:
        parser.require(words, fragment, fragment)
    for size, half in [(2, 1), (4, 2), (8, 4), (16, 8), (32, 16)]:
        parser.require(words, 'vector' + str(size) + ' = DoubleV vector' + str(half), 'word32 shape')
    bit = read(repo / 'Haskell/Core/Simplicity/Ty/Bit.hs')
    for fragment in ['toBit False = Left ()', 'toBit True = Right ()']:
        parser.require(bit, fragment, 'bit injection')
    bit = read(coq / 'Simplicity/Bit.v')
    for fragment in ['Notation "\'Bit.zero\'" := (inl tt).', 'Notation "\'Bit.one\'" := (inr tt).']:
        parser.require(bit, fragment, 'Coq bit injection')
    conversion = coq / 'C/jet_haskell_word_conversion.v'
    definition(conversion, 'haskell_word_state', '''
      match n as n return Ty.tySem (Word n) * Z with
      | O => ((if Z.odd z then Bit.one else Bit.zero), z / 2)
      | S n => let '(lo, rest) := haskell_word_state n z in
               let '(hi, final) := haskell_word_state n rest in ((hi, lo), final) end''')
    definition(conversion, 'haskell_to_word', 'fst (haskell_word_state n z)')
    source = read(literal)
    equal(parser.definition(source, 'haskell_from_word_acc'), '''
      match n as k return Z -> tySem (Word k) -> Z with
      | O => fun i w => match w with inl _ => 2 * i | inr _ => 2 * i + 1 end
      | S k => fun i w => let '(hi, lo) := w in
          haskell_from_word_acc k (haskell_from_word_acc k i hi) lo end''', 'Coq literal input decoder')
    equal(parser.definition(source, 'haskell_from_word'), 'haskell_from_word_acc n 0 a', 'decoder initial state')
    equal(parser.definition(source, 'elements_input_sequence_literal_spec'), '''
      Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | Some txi => inr (haskell_to_word 5 (Int.unsigned (sigTxiSequence txi)))
        | None => inl tt end)''', 'literal result interpretation')
    statement = re.findall(r'Theorem elements_input_sequence_literal_local_spec\s*:(.*?)\bProof\.', source, re.S)
    if len(statement) != 1:
        raise ValueError('missing/duplicate actual-C literal contract')
    equal(statement[0], '''application_jet_local_spec_sep f_simplicity_input_sequence elements_ge Elements.env Word32
      (Ty.Sum Ty.Unit Word32)
      (indexed_scalar_rep (fun e => sigTxIn (Elements.envTx e))
        (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696)
      elements_input_sequence_literal_spec.''', 'C function, program, domain, representation and whole contract')
    definition(coq / 'C/jet_elements_indexed_scalar_jets.v', 'elements_input_sequence_spec',
               'Primitive.Combinators.prim Elements.InputSequence')
    return {'selected_primitive': 'Elements.InputSequence', 'literal_word_state_reviewed': True,
            'literal_input_decoder_reviewed': True,
            'other_primitive_clauses_reviewed': False, 'normal_registration': False,
            'kernel_checked_by_this_tool': False,
            'source_sha256': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--coq', type=Path, required=True)
    parser.add_argument('--literal', type=Path, required=True)
    args = parser.parse_args()
    import json
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
