"""Selected legacy assertion programs and complete success/failure contracts.

A source correspondence guard, not caller cache construction, a host-library
theorem, a kernel checker, or normal acceptance.
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
    legacy = load('legacy_assert_getter_source', HERE.parent / 'elements-legacy-lock/check-source.py')
    r = legacy.check(repo)
    assertion = load('legacy_assert_shared_source', HERE.parent / 'elements-check-lock/check-source.py')
    a = assertion.check(repo, coq, coq / 'C/jet_elements_check_lock_literal.v',
                        coq / 'C/jet_application_partial_transport.v')
    r['source_sha256'].update(a['source_sha256'])
    p = load('legacy_assert_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('legacy assertion source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous assertion clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous assertion definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole assertion contract: ' + name)
        equal(found[0], expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    hs = read(repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs')
    for suffix in ['Distance', 'Duration']:
        tag = 'BrokenDoNotUseCheckLock' + suffix
        p.require(catalog, tag + ' :: TimeLockJet TimeLock.' + suffix + ' ()', 'selected assertion type')
        line(catalog, 'specificationTimeLock ' + tag, 'TimeLock.brokenCheckLock' + suffix)
        line(hs, 'brokenCheckLock' + suffix,
             'assert (iden &&& (unit >>> brokenTxLock' + suffix + ') >>> le word16)')
    local = coq / 'C/jet_elements_legacy_check.v'
    definition(local, 'elements_legacy_value', '''if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
      then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0''')
    definition(local, 'elements_legacy_check_spec', '''elements_assert_spec
      (elements_comp
        (elements_pair (elements_core (fun alg => @DC.iden Word16 alg))
          (elements_comp (elements_core (fun alg => @DC.unit Word16 alg)) (elements_legacy_lock_spec distance)))
        (elements_core (fun alg => @le_word_spec alg 4)))''')
    definition(local, 'elements_legacy_check_rep', 'exists fp, elements_legacy_lock_env_rep distance m env environment fp')
    definition(local, 'legacy_check_jet', '''if distance then f_simplicity_broken_do_not_use_check_lock_distance
      else f_simplicity_broken_do_not_use_check_lock_duration''')
    statement(local, 'elements_legacy_check_local_spec', '''distance :
      application_jet_partial_spec (legacy_check_jet distance) elements_ge Elements.env Word16 Ty.Unit
      (elements_legacy_check_rep distance)
      (fun a e => @elements_legacy_check_spec distance (PrimitivePrimSem option_Monad_Zero) a e).''')
    for suffix, flag in [('distance', 'true'), ('duration', 'false')]:
        statement(local, 'elements_broken_check_lock_' + suffix + '_local_spec', ''' :
          application_jet_partial_spec f_simplicity_broken_do_not_use_check_lock_''' + suffix + ''' elements_ge Elements.env Word16 Ty.Unit
          (elements_legacy_check_rep Datatypes.''' + flag + ''')
          (fun a e => @elements_legacy_check_spec Datatypes.''' + flag + ''' (PrimitivePrimSem option_Monad_Zero) a e).''')
    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    for suffix in ['Distance', 'Duration']:
        name = 'simplicity_broken_do_not_use_check_lock_' + suffix.lower()
        found = re.findall(r'bool\s+' + name + r'\s*\(frameItem\* dst, frameItem src, const txEnv\* env\)\s*\{([^{}]*)\}', c)
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual C assertion jet')
        equal(found[0], '(void) dst; uint_fast16_t x = simplicity_read16(&src); return x <= obsolete_lock' + suffix + '(env->tx);', name)
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.BrokenDoNotUseCheckLockDistance', 'Elements.BrokenDoNotUseCheckLockDuration'],
             failure_return_and_whole_contract_reviewed=True, caller_cache_construction_proved=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
