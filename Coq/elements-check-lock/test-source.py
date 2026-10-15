"""Reject assertion/failure/framing corruptions without compiling bad proofs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('check_lock_negative_source', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal, transport = map(Path, sys.argv[1:])
gate.check(repo, coq, literal, transport)
fixtures = [
    (repo / 'Haskell/Simplicity/Elements/Jets.hs',
     'specificationTimeLock CheckLockHeight = TimeLock.checkLockHeight',
     'specificationTimeLock CheckLockHeight = TimeLock.checkLockTime'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'checkLockHeight = assert (iden &&& (unit >>> txLockHeight) >>> le word32)',
     'checkLockHeight = assert (iden &&& (unit >>> txLockTime) >>> le word32)'),
    (repo / 'Haskell/Simplicity/Elements/Programs/TimeLock.hs',
     'checkLockTime = assert (iden &&& (unit >>> txLockTime) >>> le word32)',
     'checkLockTime = assert (iden &&& (unit >>> txLockTime) >>> lt word32)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Arith.hs',
     'le w = not (ih &&& oh >>> lt w)', 'le w = not (oh &&& ih >>> lt w)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Bit.hs',
     'assert t = t &&& unit >>> assertr cmrFail0 oh', 'assert t = t &&& unit >>> assertl oh cmrFail0'),
    (repo / 'Haskell/Core/Simplicity/Term/Core.hs',
     'fail0 = fail (hash0, hash0)', 'fail0 = fail (hash1, hash0)'),
    (coq / 'C/jet_order_spec.v',
     'AC.pair (AC.drop AC.iden) (AC.take AC.iden)', 'AC.pair (AC.take AC.iden) (AC.drop AC.iden)'),
    (coq / 'C/jet_elements_current_spec.v',
     'Alg.Assertion.Combinators.assertr assertion_cmr_fail0',
     'Alg.Assertion.Combinators.assertl assertion_cmr_fail0'),
    (coq / 'C/jet_elements_check_lock.v',
     'elements_check_lock_program Datatypes.true', 'elements_check_lock_program Datatypes.false'),
    (coq / 'C/jet_elements_check_lock.v',
     'elements_check_lock_program Datatypes.false', 'elements_check_lock_program Datatypes.true'),
    (coq / 'C/jet_elements_check_lock.v',
     'exists fp, elements_lock_env_rep m env environment fp', 'True'),
    (coq / 'C/jet_partial.v',
     'Some _ => Vint Int.one | None => Vint Int.zero', 'Some _ => Vint Int.one | None => Vint Int.one'),
    (coq / 'C/jet_application_partial.v',
     'E0 mf (jet_partial_return (spec a logical_env))', 'E0 mf (Vint Int.one)'),
    (coq / 'C/jet_application_partial.v',
     'read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned',
     'read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned + 1'),
    (coq / 'C/jet_application_partial.v',
     'Mem.load chunk mf b ofs = Mem.load chunk m b ofs', 'True'),
    (coq / 'C/jet_elements_check_lock.v',
     'Theorem elements_check_lock_height_local_spec :', 'Theorem elements_check_lock_height_local_spec : False ->'),
    (coq / 'C/jet_elements_check_lock.v',
     'application_jet_partial_spec f_simplicity_check_lock_time', 'application_jet_partial_spec f_simplicity_check_lock_height'),
    (literal, 'elements_assert_spec\n    ((iden', 'elements_verify_spec\n    ((iden'),
    (literal, 'unit >>> elements_lock_literal_program height', 'unit >>> elements_lock_literal_program Datatypes.false'),
    (literal, 'Theorem elements_check_lock_time_literal_local_spec :',
     'Theorem elements_check_lock_time_literal_local_spec : False ->'),
    (literal, 'application_jet_partial_spec f_simplicity_check_lock_height',
     'application_jet_local_spec f_simplicity_check_lock_height'),
    (literal, 'elements_ge Elements.env', 'elements_ge Bitcoin.env'),
    (literal, 'Word32 Ty.Unit elements_check_lock_env_rep', 'Word16 Ty.Unit elements_check_lock_env_rep'),
    (literal, '@elements_check_lock_literal_program Datatypes.true', '@elements_check_lock_literal_program Datatypes.false'),
    (transport, 'application_jet_partial_spec f ge E A B rep spec2.',
     'application_jet_partial_spec f ge E A B rep spec1.'),
]
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive check-lock corruption: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal, transport)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted check-lock corruption: ' + old)
gate.check(repo, coq, literal, transport)
print(str(len(fixtures)) + ' assertion/failure-return/framing/whole-check-lock-contract corruptions rejected')
