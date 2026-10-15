"""Selected TxIsFinal canonical program and complete actual-C contract guard.

Checks source correspondence, not compilation/kernel validity or admission.
The shared InputSequence guard supplies the primitive and word representation.
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


def check(repo, coq):
    inherited = load('finality_input_source', HERE.parent / 'elements-sequence-review/check-source.py')
    record = inherited.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v')
    parser = load('finality_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('TxIsFinal correspondence differs: ' + label)

    def line(source, start, expected):
        matches = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous TxIsFinal clause: ' + start)
        equal(matches[0], expected, start)

    def between(source, start, end, expected):
        if source.count(start) != 1 or source.count(end) != 1:
            raise ValueError('ambiguous recursive source boundary: ' + start)
        equal(source.split(start, 1)[1].split(end, 1)[0], expected, start)

    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    parser.require(catalog, 'TxIsFinal :: TimeLockJet () TimeLock.Bit', 'jet type')
    parser.require(catalog, 'import qualified Simplicity.Elements.Programs.TimeLock as TimeLock', 'program module')
    line(catalog, 'specificationTimeLock TxIsFinal', 'TimeLock.txIsFinal')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs')
    between(program, 'txIsFinal =', 'txLockHeight ::', '''
      (unit &&& unit) >>> forWhile word32 body >>> copair iden true
      where body = take (drop (primitive InputSequence)) >>> copair (injl true)
        (all word32 >>> copair (injl false) (injr unit))''')
    words = read(repo / 'Haskell/Core/Simplicity/Programs/Word.hs')
    between(words, 'all SingleV =', 'leftmost ::', '''
      iden all (DoubleV w) = and (take rec) (drop rec) where rec = all w''')
    between(words, 'forWhile SingleV body =', 'firstFail ::', '''
      (((oh &&& false) &&& ih) >>> monobody) &&& oh
        >>> match (injl oh) (((ih &&& true) &&& oh) >>> monobody)
      where monobody = body
      forWhile (DoubleV n) body = forWhile n
        (forWhile n ((oooh &&& (ooih &&& oih)) &&& ih >>> body))''')
    core = read(repo / 'Haskell/Core/Simplicity/Term/Core.hs')
    for start, expected in [('(>>>)', 'comp'), ('(&&&)', 'pair'), ('oh', 'take iden'),
                            ('ih', 'drop iden'), ('ooh', 'take oh'), ('oih', 'take ih'),
                            ('oooh', 'take ooh'), ('ooih', 'take oih'),
                            ('copair', 'elimS iden'),
                            ('elimS r s t', 'r &&& unit >>> match (take s) (take t)')]:
        line(core, start, expected)
    bit = read(repo / 'Haskell/Core/Simplicity/Programs/Bit.hs')
    for start, expected in [('false', 'injl unit'), ('true', 'injr unit'),
                            ('cond thn els', 'match (drop els) (drop thn)'),
                            ('and s t', 's &&& iden >>> cond t false')]:
        line(bit, start, expected)
    for name, expected in [('false', 'injl unit'), ('true', 'injr unit'),
                           ('cond', 'case (drop els) (drop thn)'),
                           ('and', 's &&& iden >>> cond t false')]:
        definition(coq / 'Simplicity/Bit.v', name, expected)
    definition(coq / 'Simplicity/Alg.v', 'copair', 'elimS iden')
    definition(coq / 'Simplicity/Alg.v', 'elimS', 'comp (pair r unit) (case (take s) (take t))')
    alg = read(coq / 'Simplicity/Alg.v')
    for fragment in ['Notation "s &&& t" := (pair s t)', 'Notation "s >>> t" := (comp s t)',
                     'Notation "\'H\'" := iden', 'Notation "\'O\' x" := (take x)',
                     'Notation "\'I\' x" := (drop x)']:
        parser.require(alg, fragment, 'Coq routing/term notation')
    definition(coq / 'C/jet_predicate_spec.v', 'predicate_spec', '''
      match n with | O => @Alg.Core.Combinators.iden Bit term
      | S n => let hi := @Alg.Core.Combinators.take (Word n) (Word n) Bit term (predicate_spec n all) in
        let lo := @Alg.Core.Combinators.drop (Word n) (Word n) Bit term (predicate_spec n all) in
        if all then Bit.and hi lo else Bit.or hi lo end''')
    definition(coq / 'C/jet_forWhile_spec.v', 'for_while_program', '''
      match n as k return alg ((C * Word k) * A) (B + A) -> alg (C * A) (B + A) with
      | 0 => fun body => ((((O H &&& Bit.false) &&& I H) >>> body) &&& O H) >>>
        case (injl (O H)) (((I H &&& Bit.true) &&& O H) >>> body)
      | S k => fun body => for_while_program k (for_while_program k
        (((O O O H &&& (O O I H &&& O I H)) &&& I H) >>> body)) end body''')
    spec = coq / 'C/jet_elements_is_final_spec.v'
    definition(spec, 'final_tail', '@predicate_spec 5 Datatypes.true alg >>> copair (injl Bit.false) (injr unit)')
    definition(spec, 'final_body', 'take (drop op) >>> copair (injl Bit.true) final_tail')
    definition(spec, 'final_program', '(unit &&& unit) >>> for_while_program 5 (final_body op) >>> copair iden Bit.true')
    definition(spec, 'elements_tx_is_final_spec', 'final_program (Primitive.Combinators.prim Elements.InputSequence)')
    local = coq / 'C/jet_elements_is_final_local.v'
    definition(local, 'elements_tx_is_final_env_rep', r'''
      exists be ebase bt tbase,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= tbase /\ tbase + 760 <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
        Mem.load Mint8unsigned m bt (tbase + 752) =
          Some (Vint (bool_int (forallb sequence_final (sigTxIn (Elements.envTx environment))))) /\
        fp = [(be, ebase, ebase + 8); (bt, tbase + 752, tbase + 753)]''')
    definition(local, 'bool_int', 'if b then Int.one else Int.zero')
    definition(spec, 'sequence_final', 'Z.eqb (Int.unsigned (sigTxiSequence txi)) 4294967295')
    statements = re.findall(r'Theorem elements_tx_is_final_local_spec\s*:(.*?)\bProof\.', read(local), re.S)
    if len(statements) != 1:
        raise ValueError('missing/ambiguous whole TxIsFinal C contract')
    equal(statements[0], '''
      application_jet_local_spec_sep f_simplicity_tx_is_final elements_ge Elements.env Ty.Unit Bit
        elements_tx_is_final_env_rep
        (fun a environment => @elements_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero) a environment).''',
        'whole function/environment/domain/output/framing/specification contract')
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jet='Elements.TxIsFinal', recursive_loop_reviewed=True,
                  mathematical_forallb_is_only_intermediate=True, normal_registration=False,
                  kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    args = argparse.ArgumentParser()
    args.add_argument('--repo', type=Path, required=True)
    args.add_argument('--coq', type=Path, required=True)
    options = args.parse_args()
    print(json.dumps(check(options.repo, options.coq), indent=2))
