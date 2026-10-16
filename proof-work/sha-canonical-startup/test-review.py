"""Read-only proof/source/kernel/support/command evidence corruptions."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('sha_canonical_evidence_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(changes):
    global count
    for path, raw in changes.items():
        if read_bytes(path) == raw:
            raise AssertionError('inactive SHA evidence fixture: ' + str(path))
    def text(self, *args, **kwargs):
        return changes[self].decode() if self in changes else read_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return changes[self] if self in changes else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            g.review(work)
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted SHA evidence corruption: ' + str(list(changes)))


def field(path, key, value):
    record = json.loads(read_text(path))
    record[key] = value
    reject({path: json.dumps(record).encode()})


for key, value in [
    ('modules', []), ('new_sources', []), ('results', []), ('definitions', ['unreviewed']),
    ('endpoints', []), ('closed_results', ['unreviewed']), ('freshly_compiled_support', []),
    ('whole_c_endpoints', 19), ('conditional_memcpy_endpoints', 0),
    ('inherited_endpoint_assumptions', 6), ('new_axioms', 1),
    ('existing_execution_and_startup_proofs_reused', False), ('named_original_startup_state', False),
    ('actual_initial_memory_exists', False), ('canonical_source_review_complete', True),
    ('recursive_kernel_check', False), ('normal_registration', True), ('coverage_added', 18),
    ('full_acceptance', True), ('base_checked_sha256', ''), ('base_review_sha256', ''),
    ('candidate_input_sha256', ''), ('main_inputs', {}), ('source_sha256', {}),
    ('object_sha256', {}), ('dependencies', {}), ('commands', {}), ('kernel_launch_sha256', ''),
]:
    field(HERE / 'CHECKED.json', key, value)
field(HERE / 'RUN.json', 'recursive_kernel_check', True)
for key, value in [('command', ['true']), ('compiled_receipt_sha256', ''), ('driver_sha256', '')]:
    field(HERE / 'KERNEL-RUN.json', key, value)
for key, value in [
    ('modules', []), ('results', []), ('definitions', []), ('closed_results', []),
    ('dependencies', {}), ('commands', {}), ('source_sha256', {}), ('object_sha256', {}),
    ('checked_sha256', ''), ('tool_sha256', ''), ('new_axioms', 1),
    ('full_types_and_definitions', False), ('normal_registration', True), ('coverage_added', 9),
]:
    field(HERE / 'SUPPORT-REPORT.json', key, value)
for key, value in [
    ('source_review', {}), ('candidate_input_sha256', ''), ('compile_receipt_sha256', ''),
    ('checked_receipt_sha256', ''), ('kernel_launch_sha256', ''), ('tools_sha256', {}),
    ('commands', {}), ('canonical_source_review_complete', False),
    ('prior_recursive_kernel_evidence_validated', False), ('formal_host_library_equivalence', True),
    ('independent_evidence_review_complete', True), ('normal_registration', True),
    ('coverage_added', 18), ('full_acceptance', True),
]:
    field(g.SOURCE / 'SOURCE-REVIEW.json', key, value)
for module in g.g.SUPPORT + [g.g.MODULE]:
    path = work / 'Coq' / (module.replace('.', '/') + '.v')
    reject({path: read_bytes(path) + b'\nUNREVIEWED\n'})
    reject({path.with_suffix('.vo'): read_bytes(path.with_suffix('.vo')) + b'\x00'})
for name in ['check.py', 'kernel.py', 'report-support.py']:
    path = HERE / name
    reject({path: read_bytes(path) + b'\n# changed reviewed proof tool\n'})
for name in ['check-source.py', 'test-source.py', 'source-model.py', 'create-model.py', 'finish-source.py']:
    path = g.SOURCE / name
    reject({path: read_bytes(path) + b'\n# changed reviewed source tool\n'})
for stem in json.loads(read_text(HERE / 'CHECKED.json'))['commands']:
    path = work / (stem + '.log')
    reject({path: read_bytes(path) + b'\nUNREVIEWED\n'})
for stem in ['sha-startup-support-assumptions', 'sha-startup-support-contracts', 'sha-canonical-source', 'sha-canonical-negative']:
    path = work / (stem + '.log')
    reject({path: read_bytes(path) + b'\nUNREVIEWED\n'})
for prefix in ['sha_canonical', 'sha_startup_support']:
    for kind in ['assumptions', 'contracts']:
        path = work / (prefix + '_' + kind + '.v')
        reject({path: read_bytes(path) + b'\nCheck True.\n'})
for name in ['Coq/C/jet_sha_ctx8_spec.v', 'Coq/C/jet_sha_finalize_spec.v', 'Coq/C/jet_coqchk_axioms.expected']:
    path = work / name
    reject({path: read_bytes(path) + b'\nUNREVIEWED\n'})

# Change both log copies AND the receipt's hash consistently. The actual
# kernel-context parser must reject them, not merely a copy/hash comparison.
kernel = read_text(work / 'kernel.log')
for label in ['Constants/Inductives relying on type-in-type',
              'Constants/Inductives relying on unsafe (co)fixpoints',
              'Inductives whose positivity is assumed']:
    altered = kernel.replace('* ' + label + ': <none>', '* ' + label + ': UNREVIEWED')
    if altered == kernel:
        raise AssertionError('inactive SHA unsafe-kernel fixture')
    record = json.loads(read_text(HERE / 'CHECKED.json'))
    record['commands']['kernel']['log_sha256'] = g.s.sha(altered.encode())
    reject({work / 'kernel.log': altered.encode(), HERE / 'kernel.log': altered.encode(),
            HERE / 'CHECKED.json': json.dumps(record).encode()})
with patch.object(g, 'INHERITED', g.INHERITED | {'Unreviewed.axiom'}):
    try:
        g.review(work)
    except ValueError:
        count += 1
    else:
        raise AssertionError('accepted expanded SHA dependency boundary')
# A future source-only main integration must not invalidate a real historical
# proof by making its reviewer consult the current checkout instead of bytes.
with patch.object(g.s, 'input_map', side_effect=AssertionError('historical SHA review consulted live main')):
    g.review(work)
g.review(work)
if (g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only SHA evidence tests changed private/main/index inputs')
print(str(count) + ' SHA proof/support/source/command/report/object/dependency/unsafe-kernel evidence corruptions rejected')
