"""Reject promotion, missing source/AST evidence and supplementary receipt drift."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_source_review_negative', HERE / 'review-source.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
gate.review()
r = json.loads((HERE / 'PREPARATION.json').read_text())
work = Path(r['candidate'])
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
            gate.review()
        except (ValueError, KeyError):
            count += 1
            return
        raise AssertionError('accepted corrupted supplementary source review: ' + str(path))


def field(key, value):
    def change(text):
        result = json.loads(text)
        result[key] = value
        return json.dumps(result)
    return change


for key, value in [('canonical_source_review_complete', False), ('normal_registration', True),
                   ('coverage_added', 3), ('full_acceptance', True), ('checkpoint_sha256', ''),
                   ('checkpoint_review_sha256', ''), ('candidate_input_sha256', ''), ('source_correspondence', {}),
                   ('commands', {}), ('tools_sha256', {})]:
    reject(HERE / 'PREPARATION.json', field(key, value))
reject(HERE / 'CHECKED.json', field('canonical_source_review_complete', True))
for name in ['source', 'source-negative', 'ast']:
    reject(work / (name + '.log'), lambda t: t + '\nUNREVIEWED\n')
    reject(HERE / (name + '.log'), lambda t: t + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_elements_indexed_literal.v', lambda t: t.replace('haskell_from_word 5 a', 'haskell_from_word 4 a'))
gate.review()
print(str(count) + ' supplementary source scope/promotion/command/report/AST corruptions rejected')
