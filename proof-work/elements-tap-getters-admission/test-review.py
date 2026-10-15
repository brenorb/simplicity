"""Reject in-memory normal-admission/legacy-repair/evidence corruptions."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tap_admission_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
work = Path(sys.argv[1]).resolve()
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
    raise AssertionError('accepted tap-admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('coverage_added', 3), ('full_acceptance', True), ('extensions', {}),
                   ('new_sources', []), ('coverage_additions', ''), ('baseline_inputs', {}),
                   ('main_input_sha256', ''), ('predecessor_input_sha256', ''),
                   ('predecessor_review_sha256', ''), ('proof_preparation_sha256', ''),
                   ('proof_review_sha256', ''), ('reviewed_source_generalization', {})]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('coverage_added', 3), ('full_acceptance', True), ('fresh_compiles', {}),
                   ('new_dependencies', {}), ('new_objects_sha256', {})]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('elements_tappath_u8_local_spec', 'elements_tappath_nullable_local_spec'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('name == "simplicity_tappath"', 'name == "simplicity_transaction_id"'))
reject(work / 'Coq/check-jets.sh', lambda t: t.replace('python3 elements-tap-getters/check-source.py', '# python3 elements-tap-getters/check-source.py'))
reject(work / 'Coq/check-jets.sh', lambda t: t.replace('python3 elements-tap-getters/test-source.py', '# python3 elements-tap-getters/test-source.py'))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_elements_tappath_nullable.v', lambda t: t.replace('elements_tappath_env_rep_bounded 128', 'elements_tappath_env_rep_bounded 255', 1))
reject(work / 'Coq/C/jet_elements_tappath_nullable.v', lambda t: t.replace('Theorem elements_tappath_u8_local_spec :', 'Theorem elements_tappath_u8_local_spec : False ->'))
reject(work / 'Coq/C/jet_elements_tap_getters_literal.v', lambda t: t.replace('Theorem elements_internal_key_literal_local_spec :', 'Theorem elements_internal_key_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
g.review(work)
print(str(count) + ' tap-admission/nullable-128-repair/source/printer/snapshot/evidence corruptions rejected')
