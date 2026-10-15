"""Reject in-memory evidence corruptions; never compile invalid proofs."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('direct_registry_negative', HERE / 'review.py')
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
        raise AssertionError('accepted direct-getter admission corruption: ' + str(path))


def field(key, value):
    def change(text):
        record = json.loads(text)
        record[key] = value
        return json.dumps(record)
    return change


for key, value in [('coverage_added', 100), ('coverage_additions', ''), ('extensions', {}),
                   ('new_sources', []), ('full_acceptance', True)]:
    reject(work / 'ASSEMBLY.json', field(key, value))
for key, value in [('fresh_compiles', {}), ('new_dependencies', {}),
                   ('new_objects_sha256', {}), ('full_acceptance', True)]:
    reject(work / 'PREPARATION.json', field(key, value))
reject(work / 'Coq/C/jet_coverage.tsv', lambda t: t.replace(
    'simplicity_script_cmr C.jet_elements_script_cmr_local',
    'simplicity_script_cmr C.jet_elements_genesis_hash_local'))
reject(work / 'Coq/jet-coverage.py', lambda t: t.replace(
    'output = "Word8" if name == "simplicity_tapleaf_version" else "Word256"',
    'output = "Word16"'))
reject(work / 'Coq/check-jets.sh', lambda t: t.replace(
    'python3 elements-hash-literal/check-source.py',
    '# python3 elements-hash-literal/check-source.py'))
reject(work / 'Coq/audit-jet-contracts.sh', lambda t: t.replace(
    '(explicit ? "@" : "")', '(explicit ? "" : "")'))
reject(work / 'Coq/C/jet_elements_tapleaf_literal.v', lambda t: t.replace(
    'Theorem elements_tapleaf_version_literal_local_spec :',
    'Theorem elements_tapleaf_version_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_elements_hash_literal.v', lambda t: t.replace(
    'Theorem elements_script_cmr_literal_local_spec :',
    'Theorem elements_script_cmr_literal_local_spec : False ->'))
reject(work / 'Coq/C/jet_haskell_hash_word.v', lambda t: t.replace(
    'Record haskell_word256', 'Record unreviewed_word256'))
reject(work / 'Coq/C/jet_contracts.expected', lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_assumptions.expected', lambda t: t.replace(
    ' : closed\n', ' : UNREVIEWED\n', 1))
reject(work / 'new_contracts.log', lambda t: t + '\n...\n')
reject(work / 'build.log', lambda t: t + '\nUNREVIEWED\n')
gate.review(work)
print(str(rejected) + ' direct-getter admission/source/printer/snapshot/terminal evidence corruptions rejected')
