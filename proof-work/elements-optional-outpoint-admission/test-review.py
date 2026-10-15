"""In-memory negative review of the eleven-getter virtual-predecessor delta."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('digest_admission_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, transform):
    global count
    original = read_text(path)
    altered = transform(original)
    assert original != altered, path
    def text(self, *args, **kwargs):
        return altered if self == path else read_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return altered.encode() if self == path else read_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            gate.review(work)
        except (ValueError, KeyError):
            count += 1
            return
        raise AssertionError('accepted digest admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('coverage_added', 100), ('full_acceptance', True), ('extensions', {}), ('new_sources', []),
                   ('coverage_additions', ''), ('baseline_inputs', {}), ('main_input_sha256', ''),
                   ('predecessor_input_sha256', ''), ('predecessor_review_sha256', ''), ('prior_preparations_sha256', {})]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('coverage_added', 100), ('full_acceptance', True), ('fresh_compiles', {}),
                   ('new_dependencies', {}), ('new_objects_sha256', {})]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('simplicity_input_annex_hash C.jet_elements_annex_local',
                                                          'simplicity_input_annex_hash C.jet_elements_current_gen_jets'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('Word32\\s+\\(Ty\\.Sum\\s+Ty\\.Unit\\s+Word256', 'Word64\\s+\\(Ty\\.Sum\\s+Ty\\.Unit\\s+Word256'))
for d, _ in gate.gate.GUARD_MODULES:
    reject(work / 'Coq/check-jets.sh', lambda t, n=d: t.replace('python3 ' + n + '/check-source.py', '# python3 ' + n + '/check-source.py'))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
for module, theorem in [('optional_digest_literal', 'elements_current_annex_hash_literal_local_spec'),
                         ('issuance_digest_literal', 'elements_reissuance_blinding_literal_local_spec'),
                         ('indexed_literal', 'elements_current_prev_outpoint_literal_local_spec'),
                         ('annex_local', 'elements_input_annex_hash_local_spec')]:
    reject(work / ('Coq/C/jet_elements_' + module + '.v'), lambda t, n=theorem: t.replace('Theorem ' + n + ' :', 'Theorem ' + n + ' : False ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
gate.review(work)
print(str(count) + ' digest admission/predecessor/source/printer/snapshot/evidence corruptions rejected')
