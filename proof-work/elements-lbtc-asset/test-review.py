"""Corrupt evidence in memory; never compile a weakened or invented proof."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_review_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
g.review()
receipt = HERE / 'PREPARATION.json'
r = json.loads(receipt.read_text())
work = Path(r['candidate'])
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(path, altered):
    global count
    assert read_text(path) != altered
    def text(self, *a, **kw):
        return altered if self == path else read_text(self, *a, **kw)
    def binary(self, *a, **kw):
        return altered.encode() if self == path else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            g.review()
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted corrupted lbtc evidence: ' + str(path))


for key, value in [('normal_registration', True), ('coverage_added', 1), ('full_acceptance', True),
                   ('fresh_modules', []), ('new_sources', []), ('endpoint', ''), ('results', []),
                   ('definitions', []), ('closed_shared_lemmas', []), ('dependencies', {}),
                   ('source_sha256', {}), ('object_sha256', {}), ('commands', {}), ('tools_sha256', {})]:
    reject(receipt, json.dumps({**r, key: value}))
for stem in ['lbtc-assumptions', 'lbtc-contracts', 'source', 'source-negative', 'ast', 'kernel']:
    reject(work / (stem + '.log'), read_text(work / (stem + '.log')) + '\nUNREVIEWED\n')
reject(work / 'Coq/C/jet_elements_lbtc_asset_local.v', read_text(work / 'Coq/C/jet_elements_lbtc_asset_local.v').replace(
    'Theorem elements_lbtc_asset_local_spec :', 'Theorem elements_lbtc_asset_local_spec : False ->'))
reject(work / 'Coq/C/jet_coverage.tsv', read_text(work / 'Coq/C/jet_coverage.tsv') + '\nsimplicity_lbtc_asset WRONG WRONG\n')
reject(HERE / 'lbtc-contracts.log', read_text(HERE / 'lbtc-contracts.log') + '\nUNREVIEWED\n')
g.review()
print(str(count) + ' lbtc scope/source/command/assumption/kernel/AST evidence corruptions rejected')
