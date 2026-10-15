"""Reject uncompiled in-memory corruptions of the seven-jet admission evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('seven_registry_negative', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)
read_text, read_bytes = Path.read_text, Path.read_bytes
rejected = 0


def reject(path, transform):
    global rejected
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
            rejected += 1
            return
        raise AssertionError('accepted seven-jet corruption: ' + str(path))


def field(key, value):
    def change(text):
        r = json.loads(text)
        r[key] = value
        return json.dumps(r)
    return change


for key, value in [('coverage_added', 100), ('coverage_additions', ''), ('extensions', {}),
                   ('new_sources', []), ('prior_preparations_sha256', {}), ('full_acceptance', True)]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('fresh_compiles', {}), ('new_dependencies', {}), ('new_objects_sha256', {}), ('full_acceptance', True)]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace('simplicity_input_pegin C.jet_elements_pegin_local',
                                                          'simplicity_input_pegin C.jet_elements_current_gen_jets'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace('elif name == "simplicity_input_pegin":', 'elif False:'))
for directory in ['elements-finality', 'elements-lock', 'elements-check-lock', 'elements-pegin']:
    reject(work / 'Coq/check-jets.sh', lambda t, d=directory: t.replace('python3 ' + d + '/check-source.py', '# python3 ' + d + '/check-source.py'))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace('(explicit ? "@" : "")', '(explicit ? "" : "")'))
for name, theorem in [('jet_elements_lock_literal', 'elements_tx_lock_height_literal_local_spec'),
                      ('jet_elements_check_lock_literal', 'elements_check_lock_time_literal_local_spec'),
                      ('jet_elements_pegin_literal', 'elements_current_pegin_literal_local_spec')]:
    reject(work / ('Coq/C/' + name + '.v'), lambda t, n=theorem: t.replace('Theorem ' + n + ' :', 'Theorem ' + n + ' : False ->'))
reject(work / 'Coq/C/jet_application_partial_transport.v', lambda t: t.replace('application_jet_partial_spec f ge E A B rep spec2.', 'True.'))
reject(work / 'Coq/C/jet_public_theorems.txt', lambda t: t.replace("elements_sigInput_isPegin'", 'elements_sigInput_isPegin'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
gate.review(work)
print(str(rejected) + ' seven-jet admission/source/apostrophe/printer/snapshot/terminal corruptions rejected')
