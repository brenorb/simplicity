"""In-memory corruption tests for the bounded composition import gate."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('composition_test', Path(__file__).with_name('run.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)


def kernel_command(text):
    data = json.loads(text)
    data['kernel']['command'].insert(3, '-norec')
    return json.dumps(data)


def scope(text):
    data = json.loads(text)
    data['composition_new_paths'] = []
    return json.dumps(data)


fixtures = [
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"exit_code": 0', '"exit_code": 1', 1)),
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"normal_registration": false', '"normal_registration": true')),
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"coverage_added": 0', '"coverage_added": 1')),
    (work / 'Coq/C/jet_bitcoin_env_build.v', 'read_bytes', lambda s: s.replace(b'sha_started m ->', b'True ->', 1)),
    (work / 'contracts.log', 'read_text', lambda s: s.replace('TAPENV_TYPE ', 'MISSING_TYPE ', 1)),
    (work / 'kernel.log', 'read_text', lambda s: s.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: unknown')),
    (work / 'Coq/C/jet_bitcoin_env_build.vo', 'read_bytes', lambda s: s + b'corruption'),
    (work / 'REVIEW.json', 'read_text', lambda s: s.replace('"Events.external_functions_sem"', '"Unknown.axiom"', 1)),
    (work / 'REVIEW.json', 'read_text', kernel_command),
    (work / 'ASSEMBLY.json', 'read_text', scope),
]
for target, method, mutate in fixtures:
    original = getattr(Path, method)
    target = target.resolve()
    changed = mutate(original(target))
    if changed == original(target):
        raise AssertionError('inactive corruption fixture')
    def read(self, *args, **kwargs):
        return changed if self.resolve() == target else original(self, *args, **kwargs)
    with patch.object(Path, method, read):
        try:
            gate.review(work)
        except ValueError:
            pass
        else:
            raise AssertionError('corrupt composition evidence accepted')
print('Composition source/artifact/receipt/scope corruption fixtures passed: 10')
