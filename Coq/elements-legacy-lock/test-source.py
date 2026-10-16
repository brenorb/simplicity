"""In-memory canonical/core/cache/whole-C mutations; never compile bad proofs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_negative_source', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
hs = repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs'
core = repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
spec = coq / 'C/jet_elements_legacy_lock_spec.v'
local = coq / 'C/jet_elements_legacy_lock_local.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = []
for suffix in ['Distance', 'Duration']:
    start = 'specificationTimeLock BrokenDoNotUseTxLock' + suffix + ' = TimeLock.brokenTxLock' + suffix
    fixtures.append((catalog, start, start.replace('TimeLock.brokenTxLock' + suffix, 'TimeLock.txLockHeight')))
    start = 'BrokenDoNotUseTxLock' + suffix + ' :: TimeLockJet () TimeLock.' + suffix
    fixtures.append((catalog, start, start.replace('() TimeLock.', 'Word16 TimeLock.')))
fixtures += [
    (hs, 'scribe (toWord32 2) &&& primitive Version >>> le word32', 'scribe (toWord32 3) &&& primitive Version >>> le word32'),
    (hs, 'scribe (toWord32 2) &&& primitive Version >>> le word32', 'scribe (toWord32 2) &&& primitive LockTime >>> le word32'),
    (hs, 'primitive Version >>> le word32', 'primitive Version >>> lt word32'),
    (hs, 'bip68VersionCheck &&& zero word16', 'bip68VersionCheck &&& zero word32'),
    (hs, 'forWhile word32 body >>> copair iden iden', 'forWhile word16 body >>> copair iden iden'),
    (hs, 'take (drop (primitive InputSequence)) &&& ih', 'take (drop (primitive InputPegin)) &&& ih'),
    (hs, 'match (injl ih) (injr (take parseSequence', 'match (injr ih) (injr (take parseSequence'),
    (hs, 'match ih (match (max word16) ih)', 'match ih (match ih (max word16))'),
    (hs, 'match ih (match ih (max word16))', 'match ih (match (max word16) ih)'),
    (core, 'type Distance = Word16', 'type Distance = Word32'),
    (core, 'type Duration = Word16', 'type Duration = Word32'),
    (core, 'bit31 &&& (bit22 &&& ih)', 'bit31 &&& (bit22 &&& oh)'),
    (core, 'bit31  = take (take oooh)', 'bit31  = take (take ooih)'),
    (core, 'bit22 = take (drop ooih)', 'bit22 = take (drop oooh)'),
    (core, 'cond (injr iden) (injl iden)', 'cond (injl iden) (injr iden)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs', 'max w = le w &&& iden >>> cond ih oh', 'max w = le w &&& iden >>> cond oh ih'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs', 'le w = not (ih &&& oh >>> lt w)', 'le w = not (oh &&& ih >>> lt w)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs', '(oooh &&& (ooih &&& oih)) &&& ih >>> body', '(ooih &&& (oooh &&& oih)) &&& ih >>> body'),
    (coq / 'C/jet_minmax_spec.v', 'if maximum then Bit.cond (AC.drop AC.iden) (AC.take AC.iden)', 'if maximum then Bit.cond (AC.take AC.iden) (AC.drop AC.iden)'),
    (coq / 'C/jet_order_spec.v', 'AC.pair (AC.drop AC.iden) (AC.take AC.iden)', 'AC.pair (AC.take AC.iden) (AC.drop AC.iden)'),
    (coq / 'C/jet_parse_sequence_spec.v', 'SC.take (SC.take (SC.take (SC.take (SC.take SC.iden))))', 'SC.take (SC.take (SC.take (SC.take (SC.drop SC.iden))))'),
    (coq / 'C/jet_parse_sequence_spec.v', 'SC.take (SC.drop (SC.take (SC.take (SC.drop SC.iden))))', 'SC.take (SC.drop (SC.take (SC.take (SC.take SC.iden))))'),
    (coq / 'C/jet_parse_sequence_spec.v', 'SC.pair parse_sequence_bit31 (SC.pair parse_sequence_bit22 (SC.drop SC.iden))', 'SC.pair parse_sequence_bit22 (SC.pair parse_sequence_bit31 (SC.drop SC.iden))'),
    (spec, 'case (@minmax_word_spec 4 Datatypes.true alg) (drop iden)', 'case (drop iden) (@minmax_word_spec 4 Datatypes.true alg)'),
    (spec, '(take (drop op) &&& drop iden)', '(take (drop op) &&& take iden)'),
    (spec, '(injl (drop iden))', '(injr (drop iden))'),
    (spec, 'haskell_to_word 5 2', 'haskell_to_word 5 3'),
    (spec, 'for_while_program 5 (legacy_fold_body', 'for_while_program 4 (legacy_fold_body'),
    (spec, 'legacy_version_check version &&& zero (n := 4)', 'legacy_version_check version &&& zero (n := 5)'),
    (spec, 'Primitive.Combinators.prim Elements.Version', 'Primitive.Combinators.prim Elements.LockTime'),
    (spec, 'if Z.testbit s 31 then 0', 'if Z.testbit s 30 then 0'),
    (spec, 'negb (Z.testbit s 22)', 'negb (Z.testbit s 21)'),
    (spec, 'then s mod 65536 else 0', 'then s mod 65535 else 0'),
    (spec, 'Z.max a (legacy_sequence_value', 'Z.min a (legacy_sequence_value'),
    (spec, 'xs 0.', 'xs 1.'),
    (local, 'if distance then 736 else 744', 'if distance then 744 else 736'),
    (local, 'Mem.load Mint64 m bt (base + 720)', 'Mem.load Mint64 m bt (base + 728)'),
    (local, 'Int64.unsigned ver = Int.unsigned', 'Int64.signed ver = Int.unsigned'),
    (local, 'Int64.unsigned cached = legacy_cache_value', 'Int64.unsigned cached <= legacy_cache_value'),
    (local, '(bt, base + 720, base + 752)', '(bt, base + 720, base + 744)'),
    (local, 'base + 760 <= Ptrofs.max_unsigned', 'base + 759 <= Ptrofs.max_unsigned'),
    (c, 'return 2 <= tx->version ? tx->obsolete_lockDistance : 0;', 'return 2 < tx->version ? tx->obsolete_lockDistance : 0;'),
    (c, 'return 2 <= tx->version ? tx->obsolete_lockDuration : 0;', 'return 2 <= tx->version ? tx->obsolete_lockDistance : 0;'),
    (c, 'simplicity_write16(dst, obsolete_lockDistance(env->tx));', 'simplicity_write32(dst, obsolete_lockDistance(env->tx));'),
    (c, 'simplicity_write16(dst, obsolete_lockDuration(env->tx));', 'simplicity_write16(dst, obsolete_lockDistance(env->tx));'),
]
for name in ['elements_legacy_lock_local_spec', 'elements_broken_tx_lock_distance_local_spec',
             'elements_broken_tx_lock_duration_local_spec']:
    text = local.read_text()
    start = text.index('Theorem ' + name)
    stop = text.index('Proof.', start)
    statement = text[start:stop]
    for old, new in [('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                     ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                     ('Ty.Unit Word16', 'Ty.Unit Word32'),
                     ('elements_legacy_lock_env_rep', '(fun _ _ _ _ => True)')]:
        assert old in statement, (name, old)
        fixtures.append((local, statement, statement.replace(old, new, 1)))
original = Path.read_text
g.check(repo)
for path, old, new in fixtures:
    text = original(path)
    assert old in text, ('inactive mutation', str(path), old)
    altered = text.replace(old, new, 1)
    def read(self, *a, **kw):
        return altered if self == path else original(self, *a, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted legacy lock corruption: ' + old)
g.check(repo)
print(str(len(fixtures)) + ' legacy-loop/parse/max/version/cache/whole-C corruptions rejected')
