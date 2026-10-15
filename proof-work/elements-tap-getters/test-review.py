"""Reject corrupted proof scope, old-contract comparisons and terminal evidence."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tap_review_negative', HERE / 'review.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
g.review()
receipt = HERE / 'PREPARATION.json'
r = json.loads(receipt.read_text())
work = Path(r['candidate'])
read_text, read_bytes = Path.read_text, Path.read_bytes
count = 0


def reject(changes):
    global count
    def text(self, *a, **kw):
        return changes[self] if self in changes else read_text(self, *a, **kw)
    def binary(self, *a, **kw):
        return changes[self].encode() if self in changes else read_bytes(self, *a, **kw)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            g.review()
        except (ValueError, KeyError):
            count += 1
            return
    raise AssertionError('accepted corrupted tap-getter evidence: ' + str(list(changes)))


for key, value in [('normal_registration', True), ('coverage_added', 2), ('full_acceptance', True),
                   ('roots', []), ('new_sources', []), ('reviewed_source_generalization', []),
                   ('fresh_modules', []), ('results', []), ('definitions', []), ('endpoints', []),
                   ('closed_shared_lemmas', []), ('dependencies', {}), ('baseline_results', []),
                   ('baseline_definitions', []), ('baseline_dependencies', {}), ('commands', {}),
                   ('source_sha256', {}), ('object_sha256', {}), ('tools_sha256', {})]:
    changed = {**r, key: value}
    reject({receipt: json.dumps(changed)})
for stem in ['tap-contracts', 'baseline-contracts', 'tap-assumptions', 'baseline-assumptions',
             'source', 'source-negative', 'ast', 'kernel']:
    reject({work / (stem + '.log'): read_text(work / (stem + '.log')) + '\nUNREVIEWED\n'})
    reject({HERE / (stem + '.log'): read_text(HERE / (stem + '.log')) + '\nUNREVIEWED\n'})
baseline = work / 'baseline/NullableBaseline.v'
reject({baseline: read_text(baseline).replace('<= 128', '<= 255', 1)})
source = work / 'Coq/C/jet_elements_tap_getters_literal.v'
reject({source: read_text(source).replace('Theorem elements_tappath_u8_literal_local_spec :',
                                        'Theorem elements_tappath_u8_literal_local_spec : False ->')})
# Even if forged reports have internally consistent hashes, the independent
# comparison must detect a changed legacy theorem type, not just file drift.
stem = 'baseline-contracts'
log = read_text(work / (stem + '.log')).replace(
    'NullableBaseline.elements_tappath_env_rep_nullable\n',
    'NullableBaseline.elements_tappath_env_rep_u8\n', 1)
assert log != read_text(work / (stem + '.log'))
forged = json.loads(json.dumps(r))
forged['commands'][stem]['log_sha256'] = g.s.sha(log.encode())
reject({receipt: json.dumps(forged), work / (stem + '.log'): log, HERE / (stem + '.log'): log})
g.review()
print(str(count) + ' tap-getter scope/source/old-contract/command/kernel/AST evidence corruptions rejected')
