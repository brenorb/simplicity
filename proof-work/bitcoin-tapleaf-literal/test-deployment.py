"""Postcheck exact deployed guards and reject un-fingerprinted model data."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_deployment_postcheck', HERE / 'deploy-guards.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
r = json.loads((HERE / 'GUARD-DEPLOYMENT.json').read_text())
work, base = Path(r['candidate']), Path(r['base_candidate'])
assert r['proof_review_sha256'] == g.s.sha((HERE / 'EVIDENCE-REVIEW.json').read_bytes())
assert r['original_model_sha256'] == g.s.sha((HERE / 'source-model.json').read_bytes())
assert r['tools_sha256'] == {'deploy-guards.py': g.s.sha((HERE / 'deploy-guards.py').read_bytes())}
assert r['audited_guard_targets'] == 3 and r['inherited_source_changes'] == r['proof_source_changes'] == 0
assert all(r[n] is False for n in ['full_acceptance', 'normal_registration', 'main_installation'])
for n, text in g.sources().items():
    assert (work / 'Coq' / n).read_bytes() == text.encode()
    assert r['deployed_sha256']['Coq/' + n] == g.s.sha(text.encode())
assert set(r['commands']) == {'deployed-source', 'deployed-negative'}
for stem, name in [('deployed-source', g.GUARDS[0]), ('deployed-negative', g.GUARDS[1])]:
    row = r['commands'][stem]
    assert row['command'] == [sys.executable, '-B', name, str(work)] and row['exit_code'] == 0
    assert row['log_sha256'] == g.s.sha((work / (stem + '.log')).read_bytes())
    assert (work / (stem + '.log')).read_bytes() == (HERE / (stem + '.log')).read_bytes()
inputs = g.s.load('tapleaf_deploy_postcheck_inputs', g.v.g.BASE / 'prepare-integration.py').input_map
after = inputs(base)
after.update(r['deployed_sha256'])
assert inputs(work) == after
fingerprint = g.s.inputs.fingerprint(work / 'Coq', work)
assert fingerprint == r['candidate_input_sha256']
original = Path.read_bytes
for name in g.GUARDS:
    target = work / 'Coq' / name
    def changed(self):
        raw = original(self)
        return raw + b'\nUNREVIEWED\n' if self == target else raw
    with patch.object(Path, 'read_bytes', changed):
        assert g.s.inputs.fingerprint(work / 'Coq', work) != fingerprint, 'guard omitted by normal fingerprint: ' + name
assert g.s.inputs.fingerprint(work / 'Coq', work) == fingerprint
assert g.s.index_hash() == 'f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe'
print('Exact deployed guard/model/command/log provenance checked; each of3 runtime inputs independently changes the normal fingerprint; no writes')
