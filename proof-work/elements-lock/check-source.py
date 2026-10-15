"""Selected lock-program/threshold ports and complete actual-C contracts.

Reuses the checked finality loop and LockTime primitive correspondences.
This is a source guard, not a compiler/kernel check or normal admission.
"""
import argparse
import hashlib
import importlib.util
import json
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


def check(repo, coq, literal):
    finality = load('lock_finality_source', HERE.parent / 'elements-finality/check-source.py')
    record = finality.check(repo, coq)
    getters = load('lock_primitive_source', coq / 'elements-version-review/check-getters-source.py')
    getters.check(repo, coq)
    parser = load('lock_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('Elements lock correspondence differs: ' + label)

    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)

    def line(source, start, expected):
        clauses = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(clauses) != 1:
            raise ValueError('missing/ambiguous lock clause: ' + start)
        equal(clauses[0], expected, start)

    def between(source, start, end, expected):
        if source.count(start) != 1 or source.count(end) != 1:
            raise ValueError('ambiguous lock program boundary: ' + start)
        equal(source.split(start, 1)[1].split(end, 1)[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for jet, output in [('TxLockHeight', 'Height'), ('TxLockTime', 'Time')]:
        parser.require(catalog, jet + ' :: TimeLockJet () TimeLock.' + output, 'selected jet type')
        line(catalog, 'specificationTimeLock ' + jet, 'TimeLock.' + jet[0].lower() + jet[1:])
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs')
    between(program, 'txLockHeight =', 'txLockTime ::', '''
      txIsFinal &&& primitive LockTime >>> cond z (parseLock >>> (copair iden z))
      where z = unit >>> zero word32''')
    between(program, 'txLockTime =', 'bip68VersionCheck ::', '''
      txIsFinal &&& primitive LockTime >>> cond z (parseLock >>> (copair z iden))
      where z = unit >>> zero word32''')
    shared = read(repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs')
    parser.require(shared, 'type Height = Word32', 'height width')
    parser.require(shared, 'type Time = Word32', 'time width')
    between(shared, 'parseLock =', 'parseSequence ::', '''
      (iden &&& scribe (toWord32 500000000) >>> subtract word32 >>> oh) &&& iden
        >>> cond (injl iden) (injr iden)''')
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    for fragment in ['infixr 1 >>>', 'infixr 3 &&&']:
        parser.require(core, fragment, 'source precedence/association')
    for start, expected in [('ioh', 'drop oh'), ('iih', 'drop ih')]:
        line(core, start, expected)
    arith = read(repo / 'Haskell/Core/Simplicity/Programs/Arith.hs')
    line(arith, 'zero', 'low')
    line(arith, 'subtract w', 'false &&& iden >>> full_subtract w')
    between(arith, 'full_subtract w =', '\nsubtract ::', '''
      not oh &&& drop (oh &&& (ih >>> complement w))
        >>> full_add w >>> not oh &&& ih''')
    between(arith, 'full_add SingleV =', '\nadd ::', '''
      maj &&& xor_xor
      full_add (DoubleV w) = drop (ooh &&& ioh) &&& (oh &&& drop (oih &&& iih) >>> rec)
        >>> iih &&& (ioh &&& oh >>> rec) >>> ioh &&& (iih &&& oh)
      where rec = full_add w''')
    words = read(repo / 'Haskell/Core/Simplicity/Programs/Word.hs')
    between(words, 'fill t SingleV =', '\nlow ::', '''t
      fill t (DoubleV w) = rec &&& rec where rec = fill t w''')
    line(words, 'low', 'fill false')
    between(words, 'complement SingleV =', 'bitwise_bin ::', '''not iden
      complement (DoubleV w) = take rec &&& drop rec where rec = complement w''')
    generic = read(repo / 'Haskell/Core/Simplicity/Programs/Generic.hs')
    between(generic, 'scribe =', 'eq ::', '''go reify where
      go :: (Core term, TyC a, TyC b) => TyReflect b -> b -> term a b
      go OneR () = unit
      go (SumR l _) (Left v) = injl (go l v)
      go (SumR _ r) (Right v) = injr (go r v)
      go (ProdR b1 b2) (v1, v2) = pair (go b1 v1) (go b2 v2)''')
    bit = read(repo / 'Haskell/Core/Simplicity/Programs/Bit.hs')
    for start, expected in [('not t', 't &&& unit >>> cond false true'),
                            ('xor_xor', 'cond (cond iden (not iden)) (cond (not iden) iden)'),
                            ('maj', 'cond (cond true iden) (cond iden false)')]:
        line(bit, start, expected)
    for name, expected in [('not', 't &&& unit >>> cond false true'),
                           ('xor3', 'cond (cond iden (not iden)) (cond (not iden) iden)'),
                           ('maj', 'cond (cond true iden) (cond iden false)')]:
        definition(coq / 'Simplicity/Bit.v', name, expected)
    for name, expected in [
        ('zero', 'match n with | 0 => false | S n => zero &&& zero end'),
        ('fullAdderBit', 'maj &&& xor3'),
        ('buildFullAdder', '''drop (O O H &&& I O H) &&& (O H &&& drop (O I H &&& I I H) >>> rec)
          >>> I I H &&& (I O H &&& O H >>> rec) >>> I O H &&& (I I H &&& O H)'''),
        ('fullAdder', 'match n with | 0 => fullAdderBit | S n => buildFullAdder fullAdder end'),
    ]:
        definition(coq / 'Simplicity/Word.v', name, expected)
    definition(coq / 'Simplicity/Alg.v', 'scribe', '''match B with
      | Unit => fun _ _ => unit
      | Sum BL BR => fun b => match b with
          | inl l => fun _ => injl (scribe l) | inr r => fun _ => injr (scribe r) end
      | Prod B1 B2 => fun b _ => pair (scribe (fst b)) (scribe (snd b)) end''')
    definition(coq / 'C/jet_complement_spec.v', 'complement_spec', '''match n with
      | O => @Bit.not Bit term (@Alg.Core.Combinators.iden Bit term)
      | S n => @Alg.Core.Combinators.pair (Word (S n)) (Word n) (Word n) term
          (@Alg.Core.Combinators.take (Word n) (Word n) (Word n) term (complement_spec n))
          (@Alg.Core.Combinators.drop (Word n) (Word n) (Word n) term (complement_spec n)) end''')
    definition(coq / 'C/jet_subtract_spec.v', 'full_subtract_word_spec', '''AC.comp
      (AC.pair (Bit.not (AC.take AC.iden))
        (AC.drop (AC.pair (AC.take AC.iden) (AC.comp (AC.drop AC.iden) (@complement_spec n term)))))
      (AC.comp (@Word.fullAdder n term) (AC.pair (Bit.not (AC.take AC.iden)) (AC.drop AC.iden)))''')
    definition(coq / 'C/jet_subtract_spec.v', 'subtract_word_spec',
               'AC.comp (AC.pair Bit.false AC.iden) (@full_subtract_word_spec term n)')
    definition(coq / 'C/jet_order_spec.v', 'lt_word_spec',
               'AC.comp (@subtract_word_spec term n) (AC.take AC.iden)')
    definition(coq / 'C/jet_timelock_spec.v', 'parse_lock_threshold', '@fromZ (WordToZ 5) 500000000')
    definition(coq / 'C/jet_timelock_spec.v', 'parse_lock_spec', '''TC.comp
      (TC.pair (TC.comp (TC.pair TC.iden (@Alg.scribe (Word 5) (Word 5) parse_lock_threshold term))
        (@lt_word_spec term 5)) TC.iden) (Bit.cond (TC.injl TC.iden) (TC.injr TC.iden))''')
    spec = coq / 'C/jet_elements_lock_spec.v'
    for name, expected in [
        ('lock_zero', 'unit >>> zero (n := 5)'),
        ('lock_tail', '''Bit.cond lock_zero (@parse_lock_spec alg >>>
          (if height then copair iden lock_zero else copair lock_zero iden))'''),
        ('lock_program', '(isfinal &&& locktime) >>> lock_tail height'),
        ('elements_lock_time_prim', 'Primitive.Combinators.prim Elements.LockTime'),
        ('elements_tx_lock_height_spec', 'lock_program Datatypes.true elements_tx_is_final_spec elements_lock_time_prim'),
        ('elements_tx_lock_time_spec', 'lock_program Datatypes.false elements_tx_is_final_spec elements_lock_time_prim'),
    ]:
        definition(spec, name, expected)
    for name, expected in [
        ('elements_parse_lock_literal', '''((iden &&& Alg.scribe (haskell_to_word 5 500000000)
          >>> @lt_word_spec alg 5) &&& iden) >>> Bit.cond (injl iden) (injr iden)'''),
        ('elements_lock_literal_tail', '''Bit.cond (unit >>> zero (n := 5))
          (elements_parse_lock_literal >>> (if height then copair iden (unit >>> zero (n := 5))
          else copair (unit >>> zero (n := 5)) iden))'''),
        ('elements_lock_literal_program', '''(elements_tx_is_final_spec &&& Primitive.Combinators.prim Elements.LockTime)
          >>> elements_lock_literal_tail height'''),
    ]:
        definition(literal, name, expected)
    local = coq / 'C/jet_elements_lock_local.v'
    definition(local, 'elements_lock_env_rep', r'''exists be ebase bt tbase lt,
      env = Vptr be (Ptrofs.repr ebase) /\
      0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
      0 <= tbase /\ tbase + 760 <= Ptrofs.max_unsigned /\
      Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
      Mem.load Mint8unsigned m bt (tbase + 752) =
        Some (Vint (bool_int (forallb sequence_final (sigTxIn (Elements.envTx environment))))) /\
      Mem.load Mint64 m bt (tbase + 728) = Some (Vlong lt) /\
      Int64.unsigned lt = Int.unsigned (sigTxLock (Elements.envTx environment)) /\
      fp = [(be, ebase, ebase + 8); (bt, tbase + 728, tbase + 753)]''')
    for suffix, height in [('height', 'true'), ('time', 'false')]:
        for path, infix, target in [
            (local, '', '@elements_tx_lock_' + suffix + '_spec'),
            (literal, 'literal_', '@elements_lock_literal_program Datatypes.' + height),
        ]:
            theorem = 'elements_tx_lock_' + suffix + '_' + infix + 'local_spec'
            statements = re.findall(r'Theorem ' + theorem + r'\s*:(.*?)\bProof\.', read(path), re.S)
            expected = ('application_jet_local_spec_sep f_simplicity_tx_lock_' + suffix +
                        ' elements_ge Elements.env Ty.Unit Word32 elements_lock_env_rep' +
                        ' (fun a environment => ' + target + ' (PrimitivePrimSem option_Monad_Zero) a environment).')
            if len(statements) != 1:
                raise ValueError('missing/ambiguous full C lock contract')
            equal(statements[0], expected, theorem)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.TxLockHeight', 'Elements.TxLockTime'],
                  literal_threshold_conversion_reviewed=True, normal_registration=False,
                  kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
