"""Read-only corruptions of the complete tapleaf proof/source evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_evidence_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fp = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform, binary=False):
    global count
    original = read_bytes(path) if binary else read_text(path)
    altered = transform(original)
    if original == altered:
        raise AssertionError('inactive tapleaf evidence fixture: ' + str(path))
    def text(self, *args, **kwargs):
        return altered if self == path and not binary else read_text(self, *args, **kwargs)
    def raw(self, *args, **kwargs):
        return (altered if binary else altered.encode()) if self == path else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', raw):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted tapleaf evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        row = json.loads(text)
        row[key] = value
        return json.dumps(row)
    return change


for key, value in [('modules', []), ('new_sources', []), ('results', []), ('definitions', []),
                   ('endpoints', []), ('closed_results', []), ('whole_c_endpoints', 2),
                   ('tag_derived_from_literal_ascii', False),
                   ('caller_cached_hashes_established', True), ('canonical_source_review_complete', True),
                   ('recursive_kernel_check', False), ('normal_registration', True), ('coverage_added', 1),
                   ('full_acceptance', True), ('base_checked_sha256', ''), ('base_review_sha256', ''),
                   ('candidate_input_sha256', ''), ('main_inputs', {}), ('source_sha256', {}),
                   ('object_sha256', {}), ('dependencies', {}), ('commands', {}), ('kernel_launch_sha256', '')]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(HERE / 'RUN.json', field('recursive_kernel_check', True))
reject(HERE / 'KERNEL-RUN.json', field('command', ['true']))
reject(HERE / 'KERNEL-RUN.json', field('compiled_receipt_sha256', ''))
for key, value in [('source_review', {}), ('canonical_source_review_complete', False),
                   ('compile_receipt_sha256', ''), ('candidate_input_sha256', ''),
                   ('inherited_source_review_sha256', ''), ('commands', {}),
                   ('tools_sha256', {}), ('full_acceptance', True)]:
    reject(g.SOURCE / 'SOURCE-REVIEW.json', field(key, value))
for module in [g.g.MODULE]:
    path = work / 'Coq' / (module.replace('.', '/') + '.v')
    reject(path, lambda text: text + '\nUNREVIEWED\n')
    reject(path.with_suffix('.vo'), lambda raw: raw + b'\x00', binary=True)
for stem in json.loads((HERE / 'CHECKED.json').read_text())['commands']:
    reject(work / (stem + '.log'), lambda text: text + '\nUNREVIEWED\n')
for prefix, suffix in [('elements_tapleaf', 'assumptions'), ('elements_tapleaf', 'contracts')]:
    reject(work / (prefix + '_' + suffix + '.v'), lambda text: text + '\nCheck True.\n')
for name in ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']:
    reject(g.SOURCE / name, lambda text: text + '\n# changed reviewed source tool\n')
reject(HERE / 'check.py', lambda text: text + '\n# changed proof checker\n')
reject(HERE / 'kernel.py', lambda text: text + '\n# changed kernel driver\n')
reject(work / 'Coq/C/jet_bitcoin_tapleaf_hash_spec.v', lambda text: text + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_elements_hash_getter_writehash.v', lambda text: text + '\nUNREVIEWED\n')
g.review(work)
if g.s.input_map() != before or g.s.index_hash() != index or g.s.inputs.fingerprint(work / 'Coq', work) != fp:
    raise ValueError('read-only tapleaf evidence tests changed main/index/private source')
print(str(count) + ' tapleaf proof/kernel/command/source/report/object/dependency evidence corruptions rejected')
