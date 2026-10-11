"""Small parser/normalization fixtures; never alter proof/audit candidates."""
import importlib.util
import argparse
import json
from pathlib import Path
import sys
import tempfile
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('review', Path(__file__).with_name('review-full-snapshots.py'))
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


def rejects(call):
    try:
        call()
    except (ValueError, TypeError):
        return
    raise AssertionError('malformed fixture accepted')


text = '@result\n     : forall x : nat, @eq nat x x\nInductive choice : Set := left : choice | right : choice.\n'
records = review.chunks(text, {'result', 'choice'})
assert [name for name, _ in records] == ['result', 'choice']
assert ''.join(part for _, part in records) == text
qualified = 'C.module.result\n     : True\n'
assert review.chunks(qualified, {'result'})[0][0] == 'result'
implicit = 'result ?X\n     : @eq nat O O\n'
assert review.chunks(implicit, {'result'})[0][0] == 'result'
rejects(lambda: review.chunks('', {'result'}))
rejects(lambda: review.chunks('unexpected header\n' + text, {'result', 'choice'}))
rejects(lambda: review.chunks(text + '@result\n     : False\n', {'result', 'choice'}))
rejects(lambda: review.chunks('unregistered\n     : True\n', {'result'}))
assert len(review.chunks('@result\n     : True\n@result\n     : True\n',
                         {'result'}, {'result'})) == 2
rejects(lambda: review.chunks('@result\n     : True\n' * 3, {'result'}, {'result'}))
assert review.norm('C.jet_frame_inv.finv', {'jet_frame_inv'}) == 'finv'
assert review.norm('unreviewed.finv', {'jet_frame_inv'}) == 'unreviewed.finv'
assert review.norm('BitMachine.Cell', set()) == 'Cell'
assert review.norm('BitMachine.CellCollision', set()) == 'BitMachine.CellCollision'
assert review.norm('Translate.encode', set()) == 'encode'
assert review.norm('Translate.encode_collision', set()) == 'Translate.encode_collision'
assert review.norm('False -> True', set()) != review.norm('True', set())
assert review.norm('literal_ge_negate', set()) != review.norm('numeric_ge_negate', set())

with tempfile.TemporaryDirectory(prefix='affine-snapshot-parser-') as directory:
    path = Path(directory) / 'fixture.txt'
    path.write_text('M.result : closed\nM.other : A.x, B.y\n')
    assert review.assumptions(path) == {'M.result': [], 'M.other': ['A.x', 'B.y']}
    path.write_text('M.result : closed\nM.result : A.x\n')
    rejects(lambda: review.assumptions(path))
    path.write_text('M.result closed\n')
    rejects(lambda: review.assumptions(path))
    path.write_text('M result extra\n')
    rejects(lambda: review.rows(path))
    path.write_text('M result\nM result\n')
    rejects(lambda: review.rows(path))
    assert review.rows(path, {('M', 'result')}) == [('M', 'result'), ('M', 'result')]
    path.write_text('M result\n' * 3)
    rejects(lambda: review.rows(path, {('M', 'result')}))
print('Full-snapshot parser fixtures passed: malformed records rejected; qualification/premise/specification distinctions retained')

# Optional full-context negative fixtures simulate altered report text only.
# No source, snapshot or audit input is edited, including in the frozen trees.
if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--work', type=Path)
    args = parser.parse_args()
    if args.work is not None:
        archive = Path(__file__).resolve().parent
        receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
        target = Path(receipt['candidate']) / 'Coq/C/jet_contracts.expected'
        original_read = Path.read_text
        original = target.read_text()
        header = 'ge_negate_literal_local_spec\n'
        start = original.index(header)
        prefix, public_and_defs = original[:start], original[start:]
        assert ': ' in public_and_defs and '@literal_ge_negate' in public_and_defs
        variants = [
            original.replace(': ', ': forall (_ : False), ', 1),
            prefix + public_and_defs.replace(': ', ': forall (_ : False), ', 1),
            prefix + public_and_defs.replace('@literal_ge_negate', '@canonical_fe_negate', 1),
            prefix + public_and_defs.replace('@literal_ge_negate', '@Unreviewed.literal_ge_negate', 1),
            prefix + public_and_defs.replace(header, 'unknown_public_result\n', 1),
        ]
        for changed in variants:
            assert changed != original

            def read_text(path, *a, **kw):
                return changed if path == target else original_read(path, *a, **kw)

            with patch.object(Path, 'read_text', read_text):
                rejects(lambda: review.review(archive, args.work, contracts_only=True))
        print('Five full-context report mutations rejected: inherited/new false premise, spec replacement, unknown qualification and missing public result')
