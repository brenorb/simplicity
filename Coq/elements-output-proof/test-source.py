"""In-memory proof-view/hash/index/full-contract corruptions; no bad proofs compiled."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('output_proof_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
primitive = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
indexed = coq / 'C/jet_elements_output_proof_jets.v'
fixtures = [
    (data, 'prf_ f (Explicit x) = pure (Explicit x)', 'prf_ f (Explicit x) = f x'),
    (data, 'prf_ f (Confidential pt prf) = Confidential pt <$> f prf', 'prf_ f (Confidential pt prf) = pure (Confidential pt prf)'),
    (data, 'type SurjectionProof = BSL.ByteString', 'type SurjectionProof = Hash256'),
    (data, 'type RangeProof = BSL.ByteString', 'type RangeProof = Hash256'),
    (data, 'to (Asset x) = x', 'to (Asset x) = undefined'),
    (data, 'to (Amount x) = x', 'to (Amount x) = undefined'),
    (coq / 'C/jet_elements_prim.v', '| Explicit _ => []', '| Explicit _ => [Byte.zero]'),
    (literal, 'match c with Explicit _ => [] | Confidential _ proof => proof end', 'match c with Explicit _ => [] | Confidential _ proof => [] end'),
    (literal, 'haskell_to_word 8', 'haskell_to_word 7'),
    (literal, 'byteStringHash (proof_of txo)', 'sha256_iv'),
    (coq / 'C/jet_elements_indexed_literal.v', 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
]
for name, tag, field, wrong, offset in [('surjection', 'OutputSurjectionProof', 'txoAsset', 'txoAmount', 36),
                                        ('range', 'OutputRangeProof', 'txoAmount', 'txoAsset', 68)]:
    suffix = 'output_' + name + '_proof'
    fixtures += [
        (repo / 'Haskell/Simplicity/Elements/Jets.hs', 'specificationTransaction ' + tag + ' = primitive Prim.' + tag, 'specificationTransaction ' + tag + ' = primitive Prim.OutputScriptHash'),
        (primitive, 'view (to ' + field + '.under', 'view (to ' + wrong + '.under'),
        (indexed, 'hash256_reg (byteStringHash (viewPrf (' + field + ' txo)))', 'hash256_reg sha256_iv'),
        (literal, 'elements_output_proof_digest_literal_spec (fun txo => haskell_confidential_proof_view (' + field + ' txo))', 'elements_output_proof_digest_literal_spec (fun txo => haskell_confidential_proof_view (' + wrong + ' txo))'),
    ]
    for is_literal, path in [(False, indexed), (True, literal)]:
        declaration = 'Theorem elements_' + suffix + ('_literal' if is_literal else '') + '_local_spec :'
        text = path.read_text()
        start, stop = text.index(declaration), text.index('Proof.', text.index(declaration))
        statement = text[start:stop]
        for old, new in [(declaration, declaration + ' False ->'),
                         ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                         ('248 ' + str(offset) + ' 8 704', '248 ' + str(offset + 4) + ' 8 704'),
                         ('Ty.Sum Ty.Unit Word256', 'Ty.Sum Ty.Unit Word128')]:
            if old not in statement:
                raise AssertionError('inactive selected output-proof statement: ' + old)
            fixtures.append((path, statement, statement.replace(old, new, 1)))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive output-proof mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted output-proof corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' output-proof view/hash/index/whole-C-contract corruptions rejected')
