"""Read-only refusal tests for completed proof/canonical/evidence boundaries."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_negative_review', HERE / 'review.py')
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
    raise AssertionError('accepted legacy proof/evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('candidate', ''), ('base_candidate', ''), ('base_receipt_sha256', ''),
                   ('base_input_sha256', ''), ('candidate_input_sha256', ''),
                   ('recursive_kernel_check', False), ('canonical_source_gate_complete', True),
                   ('normal_registration', True), ('full_acceptance', True), ('coverage_added', 2),
                   ('whole_c_endpoints', 1), ('execution_helpers', []), ('modules', []), ('fresh_modules', []), ('new_sources', []), ('endpoints', ['not_a_jet_endpoint']), ('results', []),
                   ('definitions', []), ('closed_results', []), ('dependencies', {}),
                   ('tools_sha256', {}), ('source_sha256', {}), ('object_sha256', {}),
                   ('main_inputs', {}), ('staged_patch_sha256', '')]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(HERE / 'RUN.json', field('recursive_kernel_check', True))


def command_bad(text):
    r = json.loads(text)
    r['commands']['kernel']['command'].append('-norec')
    return json.dumps(r)


reject(HERE / 'CHECKED.json', command_bad)
for stem in ['kernel', 'ast', 'null-output-guard-contracts', 'null-output-guard-assumptions', *g.g.ROOTS]:
    reject(work / (stem + '.log'), lambda t: t + '\nUNREVIEWED\n')
for m in g.g.ROOTS:
    reject(work / 'Coq' / (m.replace('.', '/') + '.v'), lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_haskell_hash_word.v', lambda t: t + '\nUNREVIEWED\n')
for m in g.g.ROOTS:
    path = work / 'Coq' / (m.replace('.', '/') + '.vo')
    raw = read_bytes(path)
    def binary(self, *a, **kw):
        return raw + b'UNREVIEWED' if self == path else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_bytes', binary):
        try:
            g.review(work)
        except ValueError:
            count += 1
        else:
            raise AssertionError('accepted changed fresh object: ' + m)
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only rejection tests changed main/index/private sources')
print(str(count) + ' legacy proof/assumption/type/log/source/kernel-scope corruptions rejected')
