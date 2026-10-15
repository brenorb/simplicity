"""Exercise selected recursive-source and whole-contract rejection paths."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('finality_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq = map(Path, sys.argv[1:])
gate.check(repo, coq)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTimeLock TxIsFinal = TimeLock.txIsFinal',
     'specificationTimeLock TxIsFinal = TimeLock.txLockTime'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'txIsFinal = (unit &&& unit)', 'txIsFinal = (unit &&& iden)'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'forWhile word32 body >>> copair iden true', 'forWhile word16 body >>> copair iden true'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'take (drop (primitive InputSequence))', 'take (drop (primitive InputAmount))'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'copair (injl true) (all word32', 'copair (injl false) (all word32'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     '(all word32 >>> copair (injl false) (injr unit))', '(all word32 >>> copair (injl true) (injr unit))'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'all SingleV = iden', 'all SingleV = false'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'all (DoubleV w) = and (take rec) (drop rec)', 'all (DoubleV w) = or (take rec) (drop rec)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'forWhile SingleV body = (((oh &&& false)', 'forWhile SingleV body = (((oh &&& true)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'match (injl oh) (((ih &&& true)', 'match (injr oh) (((ih &&& true)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     '(oooh &&& (ooih &&& oih))', '(oooh &&& (oih &&& ooih))'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'ooih = take oih', 'ooih = drop oih'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'copair = elimS iden', 'copair = elimS false'),
    (repo / 'Haskell/Core/Simplicity/Programs/Bit.hs',
     'and s t = s &&& iden >>> cond t false', 'and s t = s &&& iden >>> cond false t'),
    (coq / 'Simplicity/Bit.v', 's &&& iden >>> cond t false.', 's &&& iden >>> cond false t.'),
    (coq / 'Simplicity/Alg.v', 'elimS iden.', 'elimS unit.'),
    (coq / 'C/jet_forWhile_spec.v',
     'case (injl (O H))', 'case (injr (O H))'),
    (coq / 'C/jet_forWhile_spec.v',
     '(O O I H &&& O I H)', '(O I H &&& O O I H)'),
    (coq / 'C/jet_predicate_spec.v', 'if all then Bit.and hi lo', 'if all then Bit.or hi lo'),
    (coq / 'C/jet_elements_is_final_spec.v',
     '@predicate_spec 5 Datatypes.true alg', '@predicate_spec 5 Datatypes.false alg'),
    (coq / 'C/jet_elements_is_final_spec.v',
     'take (drop op) >>> copair (injl Bit.true)', 'take (drop op) >>> copair (injl Bit.false)'),
    (coq / 'C/jet_elements_is_final_spec.v',
     'for_while_program 5 (final_body op)', 'for_while_program 4 (final_body op)'),
    (coq / 'C/jet_elements_is_final_spec.v',
     'final_program (Primitive.Combinators.prim Elements.InputSequence)',
     'final_program (Primitive.Combinators.prim Elements.InputAmount)'),
    (coq / 'C/jet_elements_is_final_spec.v',
     'Z.eqb (Int.unsigned (sigTxiSequence txi)) 4294967295',
     'Z.eqb (Int.unsigned (sigTxiSequence txi)) 0'),
    (coq / 'C/jet_elements_is_final_local.v',
     'Theorem elements_tx_is_final_local_spec :', 'Theorem elements_tx_is_final_local_spec : False ->'),
    (coq / 'C/jet_elements_is_final_local.v',
     'application_jet_local_spec_sep f_simplicity_tx_is_final', 'application_jet_local_spec f_simplicity_tx_is_final'),
    (coq / 'C/jet_elements_is_final_local.v',
     'elements_ge Elements.env Ty.Unit Bit', 'elements_ge Bitcoin.env Ty.Unit Bit'),
    (coq / 'C/jet_elements_is_final_local.v',
     'elements_ge Elements.env Ty.Unit Bit', 'elements_ge Elements.env Ty.Unit Word32'),
    (coq / 'C/jet_elements_is_final_local.v',
     'Mem.load Mint8unsigned m bt (tbase + 752)', 'Mem.load Mint8unsigned m bt (tbase + 753)'),
    (coq / 'C/jet_elements_is_final_local.v',
     '(bt, tbase + 752, tbase + 753)', '(bt, tbase + 752, tbase + 754)'),
    (coq / 'C/jet_elements_is_final_local.v',
     'if b then Int.one else Int.zero', 'if b then Int.zero else Int.one'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive TxIsFinal mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted TxIsFinal corruption: ' + old)
gate.check(repo, coq)
print(str(len(fixtures)) + ' finality loop/primitive/representation/whole-C-contract corruptions rejected')
