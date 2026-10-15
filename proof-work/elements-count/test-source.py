"""In-memory corruption fixtures; never rewrite live C/Coq/Haskell inputs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
s = importlib.util.spec_from_file_location('count_source_gate', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(s)
s.loader.exec_module(gate)
repo, coq = map(Path, sys.argv[1:])
gate.check(repo, coq)
fixtures = []
for constructor, suffix, field, primitive, offset in [
    ('NumInputs', 'num_inputs', 'sigTxIn', 'InputScriptHash', '696'),
    ('NumOutputs', 'num_outputs', 'sigTxOut', 'OutputScriptHash', '704'),
]:
    accessor = 'numInputs' if constructor == 'NumInputs' else 'numOutputs'
    fixtures += [
        (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction ' + constructor + ' = Prog.' + accessor,
         'specificationTransaction ' + constructor + ' = Prog.currentIndex'),
        (repo / 'Haskell/Simplicity/Elements/Jets.hs', constructor + ' :: TransactionJet () Word32',
         constructor + ' :: TransactionJet () Word64'),
        (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'firstFail word32 (primitive ' + primitive + ')',
         'firstFail word16 (primitive ' + primitive + ')'),
        (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', accessor + ' = Transaction.' + accessor + ' Transaction.lib',
         accessor + ' = Transaction.currentIndex Transaction.lib'),
        (coq / 'C/jet_elements_count_canonical.v', 'first_fail_program 5 (Primitive.Combinators.prim Elements.' + primitive + ')',
         'first_fail_program 4 (Primitive.Combinators.prim Elements.' + primitive + ')'),
        (coq / 'C/jet_elements_count_local.v', 'Theorem elements_' + suffix + '_local_spec :',
         'Theorem elements_' + suffix + '_local_spec : False ->'),
        (coq / 'C/jet_elements_count_local.v', 'application_jet_local_spec f_simplicity_' + suffix + ' elements_ge',
         'application_jet_local_spec f_simplicity_version elements_ge'),
        (coq / 'C/jet_elements_count_local.v', 'elements_count_env_rep ' + offset,
         'elements_count_env_rep 0'),
        (coq / 'C/jet_elements_count_local.v', 'length (' + field + ' (Elements.envTx environment))',
         'length (' + ('sigTxOut' if field == 'sigTxIn' else 'sigTxIn') + ' (Elements.envTx environment))'),
    ]
fixtures += [
    (coq / 'C/jet_elements_count_local.v',
     'application_jet_local_spec f_simplicity_num_inputs elements_ge Elements.env Ty.Unit Word32',
     'application_jet_local_spec f_simplicity_num_inputs ge0 Elements.env Ty.Unit Word32'),
    (coq / 'C/jet_elements_count_local.v', 'Mem.load Mint64 m bt (txbase + delta)', 'Mem.load Mint32 m bt (txbase + delta)'),
    (coq / 'C/jet_elements_count_local.v', 'Int64.unsigned value = count environment',
     'Int64.unsigned value = count environment mod Int64.modulus'),
    (coq / 'C/jet_elements_prim.v', 'Some a => inr a', 'Some a => inl tt'),
    (coq / 'C/jet_elements_prim.v', 'None => inl tt', 'None => inr tt'),
    (coq / 'C/jet_elements_prim.v', 'nth_error (sigTxIn tx)', 'nth_error (sigTxOut tx)'),
    (coq / 'C/jet_elements_prim.v', 'Z.to_nat (toZ i)', '0%nat'),
    (coq / 'C/jet_elements_prim.v', '| InputScriptHash => atInput', '| InputScriptHash => atOutput'),
    (coq / 'C/jet_elements_prim.v', '| OutputScriptHash => atOutput', '| OutputScriptHash => atInput'),
    (coq / 'C/jet_elements_prim.v', '0 < Zlength sigTxIn < Int.modulus', '0 < Zlength sigTxIn <= Int.modulus'),
    (coq / 'C/jet_elements_prim.v', '0 <= Zlength sigTxOut < Int.modulus', '0 <= Zlength sigTxOut <= Int.modulus'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'lookupInput = (sigTxIn tx !?)', 'lookupInput = (sigTxOut tx !?)'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'atOutput f = cast . fmap f . lookupOutput',
     'atOutput f = cast . fmap f . lookupInput'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs', 'assertl (take iden) cmrFail0', 'assertr cmrFail0 (take iden)'),
    (repo / 'Haskell/Core/Simplicity/Programs/Word.hs', 'forWhile (DoubleV n) body = forWhile n (forWhile n',
     'forWhile (DoubleV n) body = forWhile n (forWhile SingleV'),
    (repo / 'Haskell/Core/Simplicity/Ty/Word.hs', 'word32 = vector32', 'word32 = vector16'),
    (coq / 'C/jet_firstFail_spec.v', 'assertl (O H) assertion_cmr_fail0', 'assertr assertion_cmr_fail0 (O H)'),
    (coq / 'C/jet_forWhile_spec.v', 'case (injl (O H))', 'case (injr (O H))'),
    (coq / 'C/jet_assertion_spec.v', '(assertion_hash0, assertion_hash0)', '(assertion_hash0, other_hash)'),
    (repo / 'C/include/simplicity/elements/env.h', 'uint32_t numInputs;', 'uint64_t numInputs;'),
    (repo / 'C/include/simplicity/elements/env.h', 'uint32_t numOutputs;', 'uint64_t numOutputs;'),
    (repo / 'C/include/simplicity/elements/env.h', 'uint32_t numInputs;',
     'uint64_t numInputs; /* uint32_t numInputs; */'),
    (repo / 'C/include/simplicity/elements/env.h', 'uint32_t numOutputs;',
     'uint64_t numOutputs; /*\nuint32_t numOutputs;\n*/'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'firstFail word32 (primitive InputScriptHash)',
     'firstFail word16 (primitive InputScriptHash) {- firstFail word32 (primitive InputScriptHash) -}'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs', 'firstFail word32 (primitive OutputScriptHash)',
     'firstFail word16 (primitive OutputScriptHash) {- firstFail word32 (primitive OutputScriptHash) -}'),
    (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'import qualified Simplicity.Elements.Programs.Transaction.Lib as Prog',
     'import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Prog'),
    (repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs', 'import qualified Simplicity.Elements.Programs.Transaction as Transaction',
     'import qualified Simplicity.Bitcoin.Programs.Transaction as Transaction'),
    (coq / 'C/jet_elements_prim.v', '| InputScriptHash => "inputScriptHash"', '| InputScriptHash => "other"'),
    (coq / 'C/jet_elements_prim.v', '| OutputScriptHash => "outputScriptHash"', '| OutputScriptHash => "other"'),
    (repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs', 'primPrefix = "Elements"', 'primPrefix = "Bitcoin"'),
]
original = Path.read_text
for target, old, new in fixtures:
    text = original(target)
    if old not in text:
        raise AssertionError('inactive fixture: ' + old)
    changed = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return changed if self == target else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq)
        except ValueError:
            pass
        else:
            raise AssertionError('count corruption accepted: ' + old)

# Hash payloads cannot affect a count: changing a total payload is deliberately
# outside the gate's observation claim, and is covered by the any-payload proof.
target = coq / 'C/jet_elements_prim.v'
text = original(target)
changed = text.replace('encodeHash (byteStringHash (utxoScript (sigTxiTxo txi)))', 'fromZ 0', 1)
assert changed != text
def read(self, *args, **kwargs):
    return changed if self == target else original(self, *args, **kwargs)
with patch.object(Path, 'read_text', read):
    gate.check(repo, coq)
gate.check(repo, coq)
print(str(len(fixtures)) + ' count source corruptions rejected; 1 observation-only payload fixture accepted')
