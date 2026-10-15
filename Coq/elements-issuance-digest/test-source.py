"""In-memory tag/field/index/current/full-contract corruptions; no invalid proofs compiled."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('issuance_digest_negative', HERE / 'check-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
repo, coq, literal = map(Path, sys.argv[1:])
gate.check(repo, coq, literal)
indexed, current = coq / 'C/jet_elements_issuance_jets.v', coq / 'C/jet_elements_current_input_jets.v'
primitive = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
fixtures = [
    (indexed, 'None => Int.repr 0', 'None => Int.repr 1'),
    (indexed, '(ofs + 272)', '(ofs + 268)'),
    (indexed, 'gh (sigTxiIssuance txi) = Some h ->', 'True ->'),
    (indexed, 'uint32_array_at m b (ofs + delta)', 'uint32_array_at m b (ofs + delta + 4)'),
    (indexed, 'match nth_error elems (Z.to_nat (toZ a))', 'match nth_error elems 0'),
    (repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs', 'type Issuance = Either NewIssuance Reissuance', 'type Issuance = Either Reissuance NewIssuance'),
    (primitive, 'cast Nothing = Left ()', 'cast Nothing = Right ()'),
    (coq / 'C/jet_elements_optional_digest_literal.v', 'haskell_from_word 5 a', 'haskell_from_word 4 a'),
    (coq / 'C/jet_elements_optional_digest_literal.v', 'haskell_to_word 8', 'haskell_to_word 7'),
]
for name, jet, camel, gh, branch, field, offset, projection in gate.FAMILIES:
    fixtures += [
        (primitive, projection, projection.replace(field.split()[0], 'newIssuanceAmount')),
        (coq / 'C/jet_elements_prim.v', '| ' + jet + ' => "' + camel + '"', '| ' + jet + ' => "wrongProjection"'),
        (indexed, 'match o with Some (' + branch + ') => Some (' + field + ')', 'match o with Some (' + branch + ') => None'),
        (literal, 'elements_input_optional_digest_literal_spec (fun txi => ' + gh + ' (sigTxiIssuance txi))', 'elements_input_optional_digest_literal_spec (fun txi => None)'),
        (literal, 'elements_current_literal_result elements_' + name + '_literal_spec', 'elements_current_literal_result elements_input_pegin_literal_spec'),
        (repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs',
         'current' + jet + ' = primitive CurrentIndex >>> assert (primitive ' + jet + ')',
         'current' + jet + ' = primitive CurrentIndex >>> assert (primitive InputPegin)'),
    ]
    for is_current, origin in [(False, indexed), (True, current)]:
        for is_literal, path in [(False, origin), (True, literal)]:
            theorem = 'elements_' + ('current_' if is_current else '') + name + ('_literal' if is_literal else '') + '_local_spec'
            declaration = 'Theorem ' + theorem + ' :'
            # Constrain type mutations to this declaration, never a later proof/definition.
            original = path.read_text()
            start = original.index(declaration)
            end = original.index('Proof.', start)
            statement = original[start:end]
            for old, new in [('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                             ('544 256 0 696', '544 256 0 704'),
                             ('issuance_hash_rep ' + str(offset) + ' ' + gh, 'issuance_hash_rep 32 ' + gh),
                             (declaration, declaration + ' False ->')]:
                if old not in statement:
                    raise AssertionError('inactive whole-contract fixture: ' + theorem)
                fixtures.append((path, statement, statement.replace(old, new, 1)))
original = Path.read_text
for path, old, new in fixtures:
    text = original(path)
    if old not in text:
        raise AssertionError('inactive issuance mutation: ' + old)
    altered = text.replace(old, new, 1)
    def read(self, *args, **kwargs):
        return altered if self == path else original(self, *args, **kwargs)
    with patch.object(Path, 'read_text', read):
        try:
            gate.check(repo, coq, literal)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted issuance corruption: ' + old)
gate.check(repo, coq, literal)
print(str(len(fixtures)) + ' issuance optional-direct-digest/tag/field/current/whole-C-contract corruptions rejected')
