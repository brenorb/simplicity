"""Selected assertion programs, failure return, and whole check-lock contracts."""
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


def check(repo, coq, literal, transport):
    lock = load('assert_lock_program_source', HERE.parent / 'elements-lock/check-source.py')
    record = lock.check(repo, coq, coq / 'C/jet_elements_lock_literal.v')
    assertion = load('assert_lock_assertion_source', coq / 'elements-current-sequence/check-source.py')
    assertion_record = assertion.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v',
                                       coq / 'C/jet_elements_current_sequence_literal.v')
    record['source_sha256'].update(assertion_record['source_sha256'])
    parser = load('assert_lock_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('check-lock source correspondence differs: ' + label)

    def line(source, start, expected):
        clauses = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(clauses) != 1:
            raise ValueError('missing/ambiguous check-lock clause: ' + start)
        equal(clauses[0], expected, start)

    def definition(path, name, expected):
        equal(parser.definition(read(path), name), expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs')
    for suffix, output in [('Height', 'Height'), ('Time', 'Time')]:
        parser.require(catalog, 'CheckLock' + suffix + ' :: TimeLockJet TimeLock.' + output + ' ()', 'assert jet type')
        line(catalog, 'specificationTimeLock CheckLock' + suffix, 'TimeLock.checkLock' + suffix)
        line(program, 'checkLock' + suffix, 'assert (iden &&& (unit >>> txLock' + suffix + ') >>> le word32)')
    arith = read(repo / 'Haskell/Core/Simplicity/Programs/Arith.hs')
    line(arith, 'lt w', 'subtract w >>> oh')
    line(arith, 'le w', 'not (ih &&& oh >>> lt w)')
    definition(coq / 'C/jet_order_spec.v', 'le_word_spec', '''
      Bit.not (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden)) (@lt_word_spec term n))''')
    local = coq / 'C/jet_elements_check_lock.v'
    definition(local, 'elements_check_lock_program', '''elements_assert_spec
      (elements_comp
        (elements_pair (elements_core (fun alg => @DC.iden (Word 5) alg))
          (elements_comp (elements_core (fun alg => @DC.unit (Word 5) alg))
            (lock_program height elements_tx_is_final_spec elements_lock_time_prim)))
        (elements_core (fun alg => @le_word_spec alg 5)))''')
    for suffix, value in [('height', 'true'), ('time', 'false')]:
        definition(local, 'elements_check_lock_' + suffix + '_spec', 'elements_check_lock_program Datatypes.' + value)
    definition(coq / 'C/jet_elements_prim_sem.v', 'elements_pair', 'DC.pair p q')
    definition(coq / 'C/jet_elements_prim_sem.v', 'elements_core', 't _')
    definition(local, 'elements_check_lock_env_rep', 'exists fp, elements_lock_env_rep m env environment fp')
    definition(coq / 'C/jet_partial.v', 'jet_partial_return',
               'match result with Some _ => Vint Int.one | None => Vint Int.zero end')
    definition(coq / 'C/jet_application_partial.v', 'application_jet_partial_spec', r'''
      forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
        env_rep m env logical_env -> frame_base_valid sbase -> (8 | sbase) ->
        frame_fields_at m bs sbase bi edge read_cursor ->
        0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
        frame_input_cells_at m bi edge read_cursor (encode a) ->
        write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
        exists mf,
          Clight2.eval_funcall ge m (Internal f)
            [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
            E0 mf (jet_partial_return (spec a logical_env)) /\
          (match spec a logical_env with
           | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\
               write_prefix_at m mf bw outedge cursor /\
               frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B))
           | None => True end) /\
          (forall chunk b ofs, Mem.valid_block m b ->
            (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
            (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
              write_word_address outedge cursor + 8 <= ofs) ->
            Mem.load chunk mf b ofs = Mem.load chunk m b ofs)''')
    definition(literal, 'elements_check_lock_literal_program', '''elements_assert_spec
      ((iden &&& (unit >>> elements_lock_literal_program height))
        >>> @le_word_spec (Primitive.CanonicalStructures.toCore alg) 5)''')
    statements = re.findall(r'Lemma application_jet_partial_spec_pointwise\b[^:]*:(.*?)\bProof\.', read(transport), re.S)
    if len(statements) != 1:
        raise ValueError('missing/ambiguous complete partial-contract transport')
    equal(statements[0], '''(forall a e, spec1 a e = spec2 a e) ->
      application_jet_partial_spec f ge E A B rep spec1 ->
      application_jet_partial_spec f ge E A B rep spec2.''', 'transport retains entire partial contract')
    for suffix, value in [('height', 'true'), ('time', 'false')]:
        for path, infix, domain, target in [
            (local, '', '(Word 5)', '@elements_check_lock_' + suffix + '_spec'),
            (literal, 'literal_', 'Word32', '@elements_check_lock_literal_program Datatypes.' + value),
        ]:
            name = 'elements_check_lock_' + suffix + '_' + infix + 'local_spec'
            statements = re.findall(r'Theorem ' + name + r'\s*:(.*?)\bProof\.', read(path), re.S)
            if len(statements) != 1:
                raise ValueError('missing/ambiguous whole check-lock C contract')
            equal(statements[0], 'application_jet_partial_spec f_simplicity_check_lock_' + suffix +
                  ' elements_ge Elements.env ' + domain + ' Ty.Unit elements_check_lock_env_rep' +
                  ' (fun a environment => ' + target + ' (PrimitivePrimSem option_Monad_Zero) a environment).', name)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.CheckLockHeight', 'Elements.CheckLockTime'],
                  failure_return_and_whole_contract_reviewed=True, normal_registration=False,
                  kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal', 'transport']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal, args.transport), indent=2))
