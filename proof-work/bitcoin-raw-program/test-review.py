"""Read-only corruptions of raw-program proof/checkpoint evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw_program_evidence_negative', HERE / 'review.py')
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
        raise AssertionError('no-op raw-program evidence fixture')
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
    raise AssertionError('accepted raw-program proof evidence corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [
    ('recursive_kernel_check', False), ('normal_registration', True), ('full_acceptance', True),
    ('coverage_added', 16), ('canonical_family_source_review_complete', True),
    ('all_caller_setup_proved', True), ('raw_data_interpretation', False), ('whole_c_endpoints', 15),
    ('fresh_modules', []), ('endpoints', []), ('closed_results', []), ('results', []),
    ('definitions', []), ('dependencies', {}), ('commands', {}), ('source_sha256', {}),
    ('object_sha256', {}), ('candidate_input_sha256', ''), ('base_input_sha256', ''),
    ('base_candidate', ''), ('base_receipt_sha256', ''), ('main_inputs_at_compile', {}),
    ('main_inputs_at_kernel', {}), ('kernel_launch_sha256', ''),
    ('staged_patch_sha256', ''), ('tools_sha256', {}),
]:
    reject(HERE / 'CHECKED.json', field(key, value))
reject(HERE / 'RUN.json', field('raw_data_interpretation', False))
reject(HERE / 'KERNEL-RUN.json', field('command', []))
for module in g.g.FRESH:
    path = work / 'Coq' / (module.replace('.', '/') + '.v')
    reject(path, lambda text: text + '\nUNREVIEWED_ACTIVE_SOURCE\n')
    reject(path.with_suffix('.vo'), lambda raw: raw + b'\x00', binary=True)
reject(work / 'raw-program-contracts.log', lambda text: text + '\n...\n')
reject(work / 'raw-program-assumptions.log',
       lambda text: text.replace('Classical_Prop.classic', 'Unreviewed.axiom'))
for name in ['kernel.log', 'ast.log', 'C.jet_bitcoin_words_hash.log',
             'raw_program_assumptions.v', 'raw_program_contracts.v']:
    reject(work / name, lambda text: text + '\nUNREVIEWED\n')
reject(HERE / 'check.py', lambda text: text + '\n# unreviewed checker\n')
reject(work / 'Coq/C/jet_application_sep.v',
       lambda text: text.replace('frame_output_cells_at mf bw outedge cursor (encode value)', 'True'))
g.review(work)
if (g.s.input_map() != before or g.s.index_hash() != index or
    g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint):
    raise ValueError('read-only raw-program evidence tests changed main/index/private sources')
print(str(count) + ' raw Bitcoin proof/source/object/type/axiom/command/scope corruptions rejected')
