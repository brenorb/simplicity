"""Read-only assertion/failure/whole-C source mutations; no bad proof compiled."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_assert_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
local = coq / 'C/jet_elements_legacy_check.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = []
for suffix in ['Distance', 'Duration']:
    clause = 'specificationTimeLock BrokenDoNotUseCheckLock' + suffix + ' = TimeLock.brokenCheckLock' + suffix
    fixtures.append((catalog, clause, clause.replace('TimeLock.brokenCheckLock' + suffix, 'TimeLock.checkLockHeight')))
    clause = 'brokenCheckLock' + suffix + ' = assert (iden &&& (unit >>> brokenTxLock' + suffix + ') >>> le word16)'
    for changed in [clause.replace('assert (', 'iden >>> ('), clause.replace('le word16', 'le word32'),
                    clause.replace('unit >>> brokenTxLock' + suffix, 'unit >>> txLockHeight')]:
        fixtures.append((hs, clause, changed))
fixtures += [
    (local, 'if 2 <=? Int.unsigned', 'if 3 <=? Int.unsigned'),
    (local, '(elements_core (fun alg => @le_word_spec alg 4))', '(elements_core (fun alg => @le_word_spec alg 5))'),
    (local, '(elements_core (fun alg => @DC.iden Word16 alg))', '(elements_core (fun alg => @DC.unit Word16 alg))'),
    (local, '(elements_legacy_lock_spec distance)', '(elements_legacy_lock_spec (negb distance))'),
    (local, 'exists fp, elements_legacy_lock_env_rep', 'forall fp, elements_legacy_lock_env_rep'),
    (local, 'then f_simplicity_broken_do_not_use_check_lock_distance', 'then f_simplicity_broken_do_not_use_check_lock_duration'),
    (coq / 'C/jet_partial.v', '| None => Vint Int.zero', '| None => Vint Int.one'),
    (c, 'return x <= obsolete_lockDistance(env->tx);', 'return x < obsolete_lockDistance(env->tx);'),
    (c, 'return x <= obsolete_lockDuration(env->tx);', 'return x <= obsolete_lockDistance(env->tx);'),
]
for name in ['elements_legacy_check_local_spec', 'elements_broken_check_lock_distance_local_spec',
             'elements_broken_check_lock_duration_local_spec']:
    text = local.read_text()
    start = text.index('Theorem ' + name)
    stop = text.index('Proof.', start)
    statement = text[start:stop]
    for old, new in [('application_jet_partial_spec', 'False -> application_jet_partial_spec'),
                     ('application_jet_partial_spec', 'application_jet_local_spec'),
                     ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                     ('Word16 Ty.Unit', 'Word32 Ty.Unit'),
                     ('elements_legacy_check_rep', '(fun _ _ _ => True)')]:
        assert old in statement, (name, old)
        fixtures.append((local, statement, statement.replace(old, new, 1)))
original = Path.read_text
g.check(repo)
for path, old, new in fixtures:
    text = original(path)
    assert old in text, ('inactive mutation', path, old)
    altered = text.replace(old, new, 1)
    def read(self, *a, **kw):
        return altered if self == path else original(self, *a, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted legacy assertion corruption: ' + old)
g.check(repo)
print(str(len(fixtures)) + ' legacy assertion/failure/cache/whole-C source corruptions rejected')
