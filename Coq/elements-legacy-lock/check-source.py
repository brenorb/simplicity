"""Selected legacy Elements loop, primitive, representation and whole-C guard.

This checks source correspondence, not a Haskell compiler/host-library theorem,
caller cache construction, kernel checking, or normal acceptance.
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
    shared = load('legacy_lock_shared_source', HERE.parent / 'elements-lock/check-source.py')
    r = shared.check(repo, coq, coq / 'C/jet_elements_lock_literal.v')
    p = load('legacy_lock_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, label):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('legacy lock source differs: ' + label)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Lemma|Theorem)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous full contract: ' + name)
        equal(found[0], expected, name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous clause: ' + name)
        equal(found[0], expected, name)

    def between(source, start, stop, expected):
        if source.count(start) != 1 or stop is not None and source.count(stop) != 1:
            raise ValueError('ambiguous source boundary: ' + start)
        body = source.split(start, 1)[1]
        equal(body.split(stop, 1)[0] if stop else body, expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for suffix in ['Distance', 'Duration']:
        tag = 'BrokenDoNotUseTxLock' + suffix
        p.require(catalog, tag + ' :: TimeLockJet () TimeLock.' + suffix, 'historical jet type')
        line(catalog, 'specificationTimeLock ' + tag, 'TimeLock.brokenTxLock' + suffix)
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs')
    line(program, 'bip68VersionCheck', 'scribe (toWord32 2) &&& primitive Version >>> le word32')
    for suffix, stop, selected in [
        ('Distance', 'brokenTxLockDuration ::', 'match (max word16) ih'),
        ('Duration', 'checkLockHeight ::', 'match ih (max word16)')]:
        between(program, 'brokenTxLock' + suffix + ' =', stop, '''
          bip68VersionCheck &&& zero word16 >>> match ih (forWhile word32 body >>> copair iden iden)
          where body = take (drop (primitive InputSequence)) &&& ih
            >>> match (injl ih) (injr (take parseSequence &&& ih >>> match ih (''' + selected + ')))')
    core = read(repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs')
    for kind in ['Distance', 'Duration']:
        p.require(core, 'type ' + kind + ' = Word16', '16-bit payload type')
    between(core, 'parseSequence =', None, '''
      bit31 &&& (bit22 &&& ih) >>> cond (injl unit) (injr (cond (injr iden) (injl iden)))
      where bit31 = take (take oooh) bit22 = take (drop ooih)''')
    arith = read(repo / 'Haskell/Core/Simplicity/Programs/Arith.hs')
    for name, expected in [('le w', 'not (ih &&& oh >>> lt w)'),
                           ('lt w', 'subtract w >>> oh'),
                           ('max w', 'le w &&& iden >>> cond ih oh')]:
        line(arith, name, expected)
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    for fragment in ['type Word16 = Vector16 Bit', 'word16 = vector16']:
        p.require(words, fragment, 'balanced 16-bit type')
    definition(coq / 'C/jet_order_spec.v', 'le_word_spec', '''Bit.not
      (AC.comp (AC.pair (AC.drop AC.iden) (AC.take AC.iden)) (@lt_word_spec term n))''')
    definition(coq / 'C/jet_minmax_spec.v', 'minmax_word_spec', '''AC.comp
      (AC.pair (@le_word_spec term n) AC.iden)
      (if maximum then Bit.cond (AC.drop AC.iden) (AC.take AC.iden)
       else Bit.cond (AC.take AC.iden) (AC.drop AC.iden))''')
    parse = coq / 'C/jet_parse_sequence_spec.v'
    for name, body in [
        ('parse_sequence_bit31', 'SC.take (SC.take (SC.take (SC.take (SC.take SC.iden))))'),
        ('parse_sequence_bit22', 'SC.take (SC.drop (SC.take (SC.take (SC.drop SC.iden))))'),
        ('parse_sequence_spec', '''SC.comp
          (SC.pair parse_sequence_bit31 (SC.pair parse_sequence_bit22 (SC.drop SC.iden)))
          (Bit.cond (SC.injl SC.unit) (SC.injr (Bit.cond (SC.injr SC.iden) (SC.injl SC.iden))))''')]:
        definition(parse, name, body)
    spec = coq / 'C/jet_elements_legacy_lock_spec.v'
    for name, body in [
        ('legacy_parse_tail', '''case (drop iden)
          (if distance then case (@minmax_word_spec 4 Datatypes.true alg) (drop iden)
           else case (drop iden) (@minmax_word_spec 4 Datatypes.true alg))'''),
        ('legacy_fold_body', '''(take (drop op) &&& drop iden) >>> case (injl (drop iden))
          (injr ((take (@parse_sequence_spec alg) &&& drop iden) >>> legacy_parse_tail distance))'''),
        ('legacy_version_check', '(Alg.scribe (haskell_to_word 5 2) &&& version) >>> @le_word_spec alg 5'),
        ('legacy_fold_finish', 'case (drop iden) (for_while_program 5 (legacy_fold_body distance op) >>> copair iden iden)'),
        ('legacy_fold_program', '(legacy_version_check version &&& zero (n := 4)) >>> legacy_fold_finish distance op'),
        ('elements_legacy_lock_spec', '''legacy_fold_program distance (Primitive.Combinators.prim Elements.Version)
          (Primitive.Combinators.prim Elements.InputSequence)'''),
        ('legacy_sequence_value', '''if Z.testbit s 31 then 0 else
          if (if distance then negb (Z.testbit s 22) else Z.testbit s 22) then s mod 65536 else 0'''),
        ('legacy_cache_value', '''fold_left (fun a x => Z.max a
          (legacy_sequence_value distance (Int.unsigned (sigTxiSequence x)))) xs 0''')]:
        definition(spec, name, body)
    local = coq / 'C/jet_elements_legacy_lock_local.v'
    for name, body in [
        ('legacy_lock_id', 'if distance then _obsolete_lockDistance else _obsolete_lockDuration'),
        ('legacy_lock_field', 'if distance then _obsolete_lockDistance else _obsolete_lockDuration'),
        ('legacy_lock_delta', 'if distance then 736 else 744'),
        ('legacy_lock_helper', 'if distance then f_obsolete_lockDistance else f_obsolete_lockDuration'),
        ('legacy_lock_jet', '''if distance then f_simplicity_broken_do_not_use_tx_lock_distance
          else f_simplicity_broken_do_not_use_tx_lock_duration''')]:
        definition(local, name, body)
    definition(local, 'elements_legacy_lock_env_rep', r'''exists be ebase bt base ver cached,
      env = Vptr be (Ptrofs.repr ebase) /\
      0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
      0 <= base /\ base + 760 <= Ptrofs.max_unsigned /\
      Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr base)) /\
      Mem.load Mint64 m bt (base + 720) = Some (Vlong ver) /\
      Int64.unsigned ver = Int.unsigned (sigTxVersion (Elements.envTx environment)) /\
      Mem.load Mint64 m bt (base + legacy_lock_delta distance) = Some (Vlong cached) /\
      Int64.unsigned cached = legacy_cache_value distance (sigTxIn (Elements.envTx environment)) /\
      fp = [(be, ebase, ebase + 8); (bt, base + 720, base + 752)]''')
    statement(local, 'elements_legacy_lock_local_spec', '''distance :
      application_jet_local_spec_sep (legacy_lock_jet distance) elements_ge Elements.env Ty.Unit Word16
        (elements_legacy_lock_env_rep distance)
        (fun a environment => @elements_legacy_lock_spec distance (PrimitivePrimSem option_Monad_Zero) a environment).''')
    for suffix, flag in [('distance', 'true'), ('duration', 'false')]:
        statement(local, 'elements_broken_tx_lock_' + suffix + '_local_spec', ''' :
          application_jet_local_spec_sep f_simplicity_broken_do_not_use_tx_lock_''' + suffix + ''' elements_ge Elements.env Ty.Unit Word16
          (elements_legacy_lock_env_rep Datatypes.''' + flag + ''')
          (fun a e => @elements_legacy_lock_spec Datatypes.''' + flag + ''' (PrimitivePrimSem option_Monad_Zero) a e).''')
    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    for suffix in ['Distance', 'Duration']:
        name = 'obsolete_lock' + suffix
        found = re.findall(r'static\s+uint_fast16_t\s+' + name + r'\s*\(const elementsTransaction\* tx\)\s*\{([^{}]*)\}', c)
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual C helper: ' + name)
        equal(found[0], 'return 2 <= tx->version ? tx->' + name + ' : 0;', name)
        name = 'simplicity_broken_do_not_use_tx_lock_' + suffix.lower()
        found = re.findall(r'bool\s+' + name + r'\s*\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c)
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual C jet: ' + name)
        equal(found[0], '(void) src; simplicity_write16(dst, obsolete_lock' + suffix + '(env->tx)); return true;', name)
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    for key in ['selected_jet', 'selected_primitive', 'other_primitive_clauses_reviewed',
                'mathematical_forallb_is_only_intermediate']:
        r.pop(key, None)
    r.update(selected_jets=['Elements.BrokenDoNotUseTxLockDistance', 'Elements.BrokenDoNotUseTxLockDuration'],
             selected_primitive_clauses=['Elements.Version', 'Elements.InputSequence'],
             literal_all_input_loop_reviewed=True, cache_representation_explicit=True,
             caller_cache_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
