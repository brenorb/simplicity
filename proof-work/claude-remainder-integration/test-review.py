"""Corruption fixtures for the additive, unregistered remainder gate."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('remainder_test', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)
meta = json.loads((work / 'ASSEMBLY.json').read_text())
entry = next(e for e in meta['modules'] if e['new'] and e['results'])
source = work / 'Coq' / entry['relative']
obj = source.with_suffix('.vo')


def edit_json(field, value):
    def mutate(text):
        data = json.loads(text)
        data[field] = value
        return json.dumps(data)
    return mutate


def no_recursive_kernel(text):
    data = json.loads(text)
    data['kernel']['command'].insert(3, '-norec')
    return json.dumps(data)


fixtures = [
    (work / 'REVIEW.json', 'read_text', edit_json('normal_registration', True)),
    (work / 'REVIEW.json', 'read_text', edit_json('coverage_added', 1)),
    (work / 'REVIEW.json', 'read_text', edit_json('source_commit', 'unreviewed')),
    (work / 'REVIEW.json', 'read_text', edit_json('canonical_source_review', 'complete')),
    (work / 'REVIEW.json', 'read_text', edit_json('results', -1)),
    (work / 'REVIEW.json', 'read_text', no_recursive_kernel),
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"exit_code": 0', '"exit_code": 1', 1)),
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"Events.external_functions_sem"', '"Unknown.axiom"', 1)),
    (work / 'ASSEMBLY.json', 'read_bytes', lambda s: s + b' '),
    (source, 'read_bytes', lambda s: s + b'\nGoal False. admit. Qed.\n'),
    (obj, 'read_bytes', lambda s: s + b'corruption'),
    (work / 'contracts.log', 'read_text', lambda s: s.replace('REMAINDER_TYPE ', 'MISSING_TYPE ', 1)),
    (work / 'kernel.log', 'read_text', lambda s: s.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: unknown')),
]
for target, method, mutate in fixtures:
    original = getattr(Path, method)
    target = target.resolve()
    corrupt = mutate(original(target))
    if corrupt == original(target):
        raise AssertionError('inactive fixture')
    def read(self, *args, **kwargs):
        return corrupt if self.resolve() == target else original(self, *args, **kwargs)
    with patch.object(Path, method, read):
        try:
            gate.review(work)
        except ValueError:
            pass
        else:
            raise AssertionError('corrupt evidence accepted: ' + str(target))

# The lexical gate must also reject escape hatches not covered by the old
# simple word list. These strings are test data, never compiled proofs.
for text in ['Axioms foo : False.', 'Parameters foo : False.', 'Goal False. Abort.',
             'Unset Guard Checking.', 'Unset Universe Checking.',
             'Proof. native_cast_no_check eq_refl. Qed.']:
    try:
        gate.safe_source(text, 'fixture')
    except ValueError:
        pass
    else:
        raise AssertionError('escape hatch accepted')
print('Remainder corruption fixtures passed: 13; lexical fixtures passed: 6')
