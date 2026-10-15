"""In-memory lock source corruptions; never compile weakened proof text."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('lock_source_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTimeLock TxLockHeight = TimeLock.txLockHeight',
     'specificationTimeLock TxLockHeight = TimeLock.txLockTime'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'cond z (parseLock >>> (copair iden z))', 'cond z (parseLock >>> (copair z iden))'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'txLockTime = txIsFinal &&& primitive LockTime', 'txLockTime = txIsFinal &&& primitive Version'),
    (repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs',
     'toWord32  500000000', 'toWord32  500000001'),
    (repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs',
     'subtract word32 >>> oh', 'subtract word32 >>> ih'),
    (repo / 'Haskell/Core/Simplicity/Programs/TimeLock.hs',
     'cond (injl iden) (injr iden)', 'cond (injr iden) (injl iden)'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'infixr 1 >>>', 'infixl 1 >>>'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs', 'ioh = drop oh', 'ioh = take oh'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
     'subtract w = false &&& iden', 'subtract w = true &&& iden'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
     'full_subtract w = not oh', 'full_subtract w = oh'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
     'full_add SingleV = maj &&& xor_xor', 'full_add SingleV = xor_xor &&& maj'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
     'full_add (DoubleV w) = drop (ooh &&& ioh)', 'full_add (DoubleV w) = drop (ioh &&& ooh)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs', 'low = fill false', 'low = fill true'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'fill t (DoubleV w) = rec &&& rec', 'fill t (DoubleV w) = rec >>> rec'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs',
     'complement SingleV = not iden', 'complement SingleV = iden'),
    (repo / 'Haskell/Core/Simplicity/Programs/Generic.hs',
     'go (SumR l _)    (Left v)  = injl (go l v)', 'go (SumR l _)    (Left v)  = injr (go l v)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Bit.hs',
     'maj = cond (cond true iden) (cond iden false)', 'maj = cond (cond false iden) (cond iden true)'),
    (coq / 'Simplicity/Word.v', '| 0 => fullAdderBit', '| 0 => adderBit'),
    (coq / 'C/jet_complement_spec.v',
     '@Bit.not Bit term (@Alg.Core.Combinators.iden Bit term)', '@Alg.Core.Combinators.iden Bit term'),
    (coq / 'C/jet_subtract_spec.v',
     'AC.comp (AC.pair Bit.false AC.iden) (@full_subtract_word_spec term n)',
     'AC.comp (AC.pair Bit.true AC.iden) (@full_subtract_word_spec term n)'),
    (coq / 'C/jet_order_spec.v',
     'AC.comp (@subtract_word_spec term n) (AC.take AC.iden)',
     'AC.comp (@subtract_word_spec term n) (AC.drop AC.iden)'),
    (coq / 'C/jet_timelock_spec.v',
     '@fromZ (WordToZ 5) 500000000', '@fromZ (WordToZ 5) 500000001'),
    (coq / 'C/jet_elements_lock_spec.v',
     'lock_program Datatypes.true elements_tx_is_final_spec',
     'lock_program Datatypes.false elements_tx_is_final_spec'),
    (coq / 'C/jet_elements_lock_local.v',
     'Theorem elements_tx_lock_height_local_spec :',
     'Theorem elements_tx_lock_height_local_spec : False ->'),
    (coq / 'C/jet_elements_lock_local.v',
     'Mem.load Mint64 m bt (tbase + 728)', 'Mem.load Mint64 m bt (tbase + 720)'),
    (coq / 'C/jet_elements_lock_local.v',
     '(bt, tbase + 728, tbase + 753)', '(bt, tbase + 728, tbase + 752)'),
    (literal, 'haskell_to_word 5 500000000', 'haskell_to_word 4 500000000'),
    (literal, 'elements_tx_is_final_spec &&& Primitive.Combinators.prim Elements.LockTime',
     'elements_tx_is_final_spec &&& Primitive.Combinators.prim Elements.Version'),
    (literal, 'Theorem elements_tx_lock_time_literal_local_spec :',
     'Theorem elements_tx_lock_time_literal_local_spec : False ->'),
    (literal, 'application_jet_local_spec_sep f_simplicity_tx_lock_time',
     'application_jet_local_spec_sep f_simplicity_tx_lock_height'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, 'Ty.Unit Word32 elements_lock_env_rep', 'Ty.Unit Word16 elements_lock_env_rep'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive lock mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted lock corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' lock/parse/subtraction/constant/representation/whole-C-contract corruptions rejected')
