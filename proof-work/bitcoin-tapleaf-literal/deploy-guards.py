"""Deploy reviewed guard data under an extension the normal audit fingerprints.

Keep the historical proof-work JSON/tools/receipts immutable. Only the exact
model filename changes in two deployed tools; no proof or model body changes.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_deployment_source', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s = v.s
GUARDS = ['bitcoin-tapleaf-literal/' + n for n in ['check-source.py', 'test-source.py', 'source-model.txt']]


def sources():
    result = {}
    for name in ['check-source.py', 'test-source.py']:
        text = (HERE / name).read_text()
        if text.count("'source-model.json'") != 1:
            raise ValueError('unexpected model-path deployment boundary')
        result['bitcoin-tapleaf-literal/' + name] = text.replace("'source-model.json'", "'source-model.txt'", 1)
    result[GUARDS[-1]] = (HERE / 'source-model.json').read_text()
    return result


def trial():
    if (HERE / 'GUARD-DEPLOYMENT.json').exists():
        raise ValueError('deployment trial already completed; inspect recorded tree/receipt')
    receipt = json.loads((HERE / 'EVIDENCE-REVIEW.json').read_text())
    base = Path(receipt['review']['candidate'])
    if receipt['review'] != v.review(base):
        raise ValueError('reviewed proof source changed')
    for n, h in receipt['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('reviewed source tool/model changed')
    before, index = s.input_map(), s.index_hash()
    inputs = s.load('tapleaf_deploy_input_map', v.g.BASE / 'prepare-integration.py').input_map
    baseline = inputs(base)
    work = Path(tempfile.mkdtemp(prefix='jet-tapleaf-guards.', dir='/private/tmp'))
    subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
    for n in ['C', 'Haskell']:
        (work / n).symlink_to(s.REPO / n, target_is_directory=True)
    selected = sources()
    if set(selected) != set(GUARDS) or any((work / 'Coq' / n).exists() for n in GUARDS):
        raise ValueError('guard trial would overwrite inherited input')
    s.changed({work / 'Coq' / n: text for n, text in selected.items()})
    after = dict(baseline)
    after.update({'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in GUARDS})
    if inputs(work) != after:
        raise ValueError('normal fingerprint inventory misses guard data or changed inherited source')
    if (work / 'Coq' / GUARDS[-1]).read_bytes() != (HERE / 'source-model.json').read_bytes():
        raise ValueError('deployed model data differs')
    commands = {}
    for stem, name in [('deployed-source', GUARDS[0]), ('deployed-negative', GUARDS[1])]:
        commands[stem] = s.run(work, [sys.executable, '-B', name, str(work)], stem, 180)
    if inputs(work) != after or s.input_map() != before or s.index_hash() != index:
        raise ValueError('guard deployment trial changed main/index/source')
    record = dict(candidate=str(work), base_candidate=str(base),
        proof_review_sha256=s.sha((HERE / 'EVIDENCE-REVIEW.json').read_bytes()),
        original_model_sha256=s.sha((HERE / 'source-model.json').read_bytes()),
        deployed_sha256={'Coq/' + n: after['Coq/' + n] for n in GUARDS},
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work), commands=commands,
        tools_sha256={'deploy-guards.py': s.sha(Path(__file__).read_bytes())},
        audited_guard_targets=3, inherited_source_changes=0, proof_source_changes=0,
        full_acceptance=False, normal_registration=False, main_installation=False)
    s.changed({HERE / 'GUARD-DEPLOYMENT.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Deployed guards and87 mutations passed; all3 runtime inputs are fingerprinted; no proof/main/registration change', flush=True)


if __name__ == '__main__':
    if sys.argv[1:] != ['trial']:
        raise ValueError('usage: deploy-guards.py trial')
    trial()
