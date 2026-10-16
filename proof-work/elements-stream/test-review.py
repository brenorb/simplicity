"""Read-only mutations of the two proof phases and their source/kernel evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_stream_evidence_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
before, index = g.s.input_map(), g.s.index_hash()
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
g.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform, binary=False):
    global count
    original = read_bytes(path) if binary else read_text(path)
    altered = transform(original)
    if altered == original:
        raise AssertionError('inactive/no-op Elements stream evidence fixture: ' + str(path))
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
    raise AssertionError('accepted Elements stream proof-evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [
    ('recursive_kernel_check', False), ('normal_registration', True), ('full_acceptance', True),
    ('coverage_added', 7), ('canonical_family_source_review_complete', True),
    ('caller_cached_hashes_established', True), ('literal_programs_over_raw_elements_data', False),
    ('whole_c_endpoints', 6), ('modules', []), ('fresh_modules', []), ('endpoints', []),
    ('closed_results', []), ('results', []), ('definitions', []), ('dependencies', {}),
    ('commands', {}), ('source_sha256', {}), ('object_sha256', {}), ('candidate_input_sha256', ''),
    ('base_candidate', ''), ('base_acceptance_sha256', ''), ('reader_checkpoint_sha256', ''),
    ('main_inputs_at_compile', {}), ('main_inputs_at_kernel', {}), ('kernel_launch_sha256', ''),
    ('staged_patch_sha256', ''), ('tools_sha256', {}),
]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(HERE / 'RUN.json', field('whole_c_endpoints', 6))
reject(HERE / 'KERNEL-RUN.json', field('command', []))
for key, value in [('any_environment_type', False), ('whole_c_endpoints', 1),
                   ('candidate_input_sha256', ''), ('source_sha256', ''), ('object_sha256', ''),
                   ('main_inputs', {}), ('closed_results', []), ('dependencies', {}), ('commands', {})]:
    reject(HERE / 'READER-CHECKED.json', field(key, value))
for module in g.g.FRESH:
    path = work / 'Coq' / (module.replace('.', '/') + '.v')
    reject(path, lambda text: text + '\nUNREVIEWED_ACTIVE_SOURCE\n')
    reject(path.with_suffix('.vo'), lambda raw: raw + b'\x00', binary=True)
for name in ['elements-stream-contracts.log', 'elements-reader-contracts.log']:
    reject(work / name, lambda text: text + '\n...\n')
for name in ['elements-stream-assumptions.log', 'elements-reader-assumptions.log']:
    reject(work / name, lambda text: text.replace(
        'FunctionalExtensionality.functional_extensionality_dep', 'Unreviewed.axiom'))
for name in ['kernel.log', 'ast.log', 'C.jet_elements_hash_getter_local.log',
             'elements_stream_assumptions.v', 'elements_stream_contracts.v',
             'elements_reader_assumptions.v', 'elements_reader_contracts.v']:
    reject(work / name, lambda text: text + '\nUNREVIEWED\n')
for name in ['check.py', 'check-reader.py']:
    reject(HERE / name, lambda text: text + '\n# changed phase checker\n')
for key, value in [('canonical_source_review_complete', False), ('coverage_added', 7),
                   ('normal_registration', True), ('full_acceptance', True),
                   ('recursive_kernel_result_checked_by_this_tool', True),
                   ('compile_receipt_sha256', ''), ('source_review', {}), ('commands', {}), ('tools_sha256', {})]:
    reject(g.SOURCE / 'SOURCE-REVIEW.json', field(key, value))
for name in ['check-source.py', 'test-source.py', 'source-model.py', 'finish-source.py']:
    reject(g.SOURCE / name, lambda text: text + '\n# changed reviewed source tool/model\n')
reject(work / 'Coq/C/jet_application_sep.v', lambda text: text.replace(
    'frame_output_cells_at mf bw outedge cursor (encode value)', 'True'))
g.review(work)
if (g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only Elements stream evidence tests changed main/index/private sources')
print(str(count) + ' Elements stream/Reader-phase/source/object/type/axiom/command/kernel/scope corruptions rejected')
