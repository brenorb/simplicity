"""Read-only source/full-type/assumption/command/scope corruption tests."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('application_lift_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform):
    global count
    original = read_text(path)
    altered = transform(original)
    assert original != altered, path
    def text(self, *a, **kw):
        return altered if self == path else read_text(self, *a, **kw)
    def binary(self, *a, **kw):
        return altered.encode() if self == path else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted application lifting evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('recursive_kernel_check', False), ('normal_registration', True), ('coverage_added', 2),
                   ('full_acceptance', True), ('concrete_jet_examples', 0), ('requires_nonempty_output', False),
                   ('results', []), ('dependencies', {}), ('commands', {}), ('source_sha256', {}),
                   ('object_sha256', {}), ('candidate_input_sha256', ''), ('staged_patch_sha256', ''),
                   ('base_receipt_sha256', ''), ('tools_sha256', {})]:
    reject(HERE / 'CHECKED.json', field(key, value))
for n in g.g.MODULES:
    reject(work / 'Coq' / (n.replace('.', '/') + '.v'), lambda t: t + '\nUNREVIEWED\n')
reject(work / 'application-context-lift-contracts.log', lambda t: t + '\n...\n')
reject(work / 'application-context-lift-assumptions.log', lambda t: t.replace('Classical_Prop.classic', 'Unreviewed.axiom'))
reject(work / 'kernel.log', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_application_context_contract.v', lambda t: t.replace('bm_separated L s', 'True'))
reject(HERE / 'check.py', lambda t: t + '\n# unreviewed checker\n')
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only review tests changed main/index/candidate')
print(str(count) + ' shared-lift source/type/axiom/command/scope corruptions rejected')
