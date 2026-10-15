"""Source-only integration of the reviewed thirteen-getter delta.

Planning is read-only and is not acceptance. Installation requires both real
terminal acceptances. Post-installation validation does not rerun a predecessor
postcheck against a different successor source tree.
"""
import difflib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRED = HERE.parent / 'elements-digest-getters-admission'
sp = importlib.util.spec_from_file_location('thirteen_integration_review', HERE / 'review.py')
review = importlib.util.module_from_spec(sp)
sp.loader.exec_module(review)
gate, s = review.gate, review.support
MARKER = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
COMMAND = ['bash', 'check-jets.sh', '--accept']


def read(path):
    if not path.is_file():
        raise ValueError('required receipt is missing: ' + str(path))
    return json.loads(path.read_text())


def terminal(path, scope, fingerprint):
    r = read(path)
    log = Path(r['log'])
    if (r['exit_code'] != 0 or r[scope] is not True or r['command'] != COMMAND or
        r['audit_input_sha256'] != fingerprint or s.sha(log.read_bytes()) != r['log_sha256'] or
        not log.read_text().rstrip().endswith(MARKER)):
        raise ValueError('terminal acceptance scope/input/command/log differs: ' + str(path))
    return r


def targets():
    result = gate.METADATA + gate.SCRIPTS + gate.GUARDS + gate.NEW_SOURCES
    if (len(result) != 23 or len(set(result)) != 23 or
        (len(gate.METADATA), len(gate.SCRIPTS), len(gate.GUARDS), len(gate.NEW_SOURCES)) != (7, 4, 8, 4)):
        raise ValueError('unexpected installation delta')
    for name in result:
        p = Path(name)
        if p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'}:
            raise ValueError('unsafe/non-source installation target')
        if not (gate.MAIN.resolve() in (gate.MAIN / p).resolve().parents):
            raise ValueError('installation target escapes main source tree')
    return result


def source_delta(before_coq, after_coq, paths):
    return ''.join(line for name in paths for line in difflib.unified_diff(
        (before_coq / name).read_text().splitlines(True) if (before_coq / name).exists() else [],
        (after_coq / name).read_text().splitlines(True),
        fromfile='a/Coq/' + name if (before_coq / name).exists() else '/dev/null',
        tofile='b/Coq/' + name))


def reviewed_evidence(work):
    r = read(work / 'REVIEW.json')
    if r['full_acceptance'] is not False or r['review']['coverage_added'] != 13:
        raise ValueError('review confused with acceptance')
    for name, digest in r['tools_sha256'].items():
        if s.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('reviewed tool drift: ' + name)
    for name, digest in r['evidence_sha256'].items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('reviewed source/object/terminal evidence drift: ' + name)
    if s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256']:
        raise ValueError('reviewed candidate source changed')
    return r


def predecessor():
    ledger = read(PRED / 'INSTALLATION.json')
    if (ledger['coverage'] != '386/533' or ledger['coverage_added'] != 8 or
        ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
        ledger['candidate_input_sha256'] != gate.PRED_REVIEW['candidate_input_sha256']):
        raise ValueError('wrong historical predecessor installation')
    isolated = Path(ledger['candidate'])
    receipt = isolated / 'ACCEPTANCE.json'
    if (ledger['isolated_acceptance_sha256'] != s.sha(receipt.read_bytes()) or
        receipt.read_bytes() != (PRED / 'ACCEPTANCE.json').read_bytes()):
        raise ValueError('predecessor isolated receipt changed')
    terminal(receipt, 'full_acceptance', ledger['candidate_input_sha256'])
    actual = terminal(PRED / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', ledger['candidate_input_sha256'])
    older = PRED.parent / 'elements-timelock-pegin-admission/MAIN-ACCEPTANCE.json'
    if ledger['prior_seven_main_acceptance_sha256'] != s.sha(older.read_bytes()):
        raise ValueError('historical prerequisite acceptance changed')
    terminal(older, 'actual_main_acceptance', ledger['before_input_sha256'])
    if s.inputs.fingerprint(isolated / 'Coq', isolated) != ledger['candidate_input_sha256']:
        raise ValueError('accepted predecessor source changed')
    return ledger, actual


def candidate_acceptance(work):
    r = reviewed_evidence(work)
    a = terminal(work / 'ACCEPTANCE.json', 'full_acceptance', r['candidate_input_sha256'])
    if (a['coverage'] != '399/533' or a['candidate'] != str(work) or
        a['review_sha256'] != s.sha((work / 'REVIEW.json').read_bytes()) or
        a['driver_sha256'] != s.sha((HERE / 'accept.py').read_bytes()) or
        a['predecessor_acceptance_sha256'] != s.sha((PRED / 'ACCEPTANCE.json').read_bytes()) or
        a['predecessor_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        (work / 'ACCEPTANCE.json').read_bytes() != (HERE / 'ACCEPTANCE.json').read_bytes()):
        raise ValueError('candidate acceptance identity/provenance differs')
    return r, a


def plan(work):
    """Exact source delta only. This function neither accepts nor installs it."""
    review.review(work)
    reviewed_evidence(work)
    meta = read(work / 'ASSEMBLY.json')
    before = review.baseline_inputs()
    if (meta['baseline_inputs'] != before or s.input_map() != before or
        s.index_hash() != meta['staged_patch_sha256'] or
        meta['predecessor_input_sha256'] != gate.PRED_REVIEW['candidate_input_sha256']):
        raise ValueError('main/predecessor/index is not the exact reviewed baseline')
    paths = targets()
    for name in gate.NEW_SOURCES + gate.GUARDS:
        if (gate.MAIN / name).exists():
            raise ValueError('new source/guard target already exists: ' + name)
    delta = source_delta(gate.MAIN, work / 'Coq', paths)
    if delta != source_delta(gate.BASE, work / 'Coq', paths):
        raise ValueError('actual-main preimage differs from the accepted predecessor source')
    installed = {'Coq/' + name: s.sha((work / 'Coq' / name).read_bytes()) for name in paths}
    return dict(candidate=str(work), before_inputs=before, targets=paths, installed_sha256=installed,
                staged_patch_sha256=meta['staged_patch_sha256'],
                before_input_sha256=meta['predecessor_input_sha256'],
                candidate_input_sha256=read(work / 'REVIEW.json')['candidate_input_sha256'],
                source_only_delta=delta, coverage='399/533', coverage_added=13,
                main_installation=False, actual_main_acceptance=False)


def install(work):
    if (HERE / 'INSTALLATION.json').exists():
        raise ValueError('one-time thirteen-getter installation already performed')
    # Check real terminal receipts before any planning, writes or installation.
    predecessor()
    _, accepted = candidate_acceptance(work)
    post = s.load('thirteen_predecessor_postcheck', PRED / 'post-check.py')
    if post.check()['actual_main_acceptance'] is not True:
        raise ValueError('actual-main predecessor has not passed')
    p = plan(work)
    if p['candidate_input_sha256'] != accepted['audit_input_sha256']:
        raise ValueError('planned source differs from accepted candidate')
    ledger = {n: p[n] for n in ['candidate', 'installed_sha256', 'staged_patch_sha256',
              'before_input_sha256', 'candidate_input_sha256', 'coverage', 'coverage_added']}
    ledger.update(main_installation=True, actual_main_acceptance=False,
        predecessor_main_acceptance_sha256=s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        predecessor_installation_sha256=s.sha((PRED / 'INSTALLATION.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        reviewed_candidate_sha256=s.sha((work / 'REVIEW.json').read_bytes()),
        integration_driver_sha256=s.sha(Path(__file__).read_bytes()),
        delta_sha256=s.sha(p['source_only_delta'].encode()))
    changes = {gate.MAIN / name: (work / 'Coq' / name).read_text() for name in p['targets']}
    changes[HERE / 'DELTA.patch'] = p['source_only_delta']
    changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    s.changed(changes)
    expected = dict(p['before_inputs'])
    expected.update(p['installed_sha256'])
    if s.input_map() != expected or s.index_hash() != p['staged_patch_sha256']:
        raise ValueError('installation changed unrelated sources or staging')
    if s.inputs.fingerprint(gate.MAIN, gate.REPO) != accepted['audit_input_sha256']:
        raise ValueError('main is not source-identical to the accepted 399 candidate')
    return check()


def check():
    ledger = read(HERE / 'INSTALLATION.json')
    work = Path(ledger['candidate'])
    old, actual = predecessor()
    _, accepted = candidate_acceptance(work)
    installed = {'Coq/' + name: s.sha((work / 'Coq' / name).read_bytes()) for name in targets()}
    if (ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
        ledger['coverage'] != '399/533' or ledger['coverage_added'] != 13 or ledger['installed_sha256'] != installed or
        ledger['before_input_sha256'] != old['candidate_input_sha256'] or
        ledger['before_input_sha256'] != actual['audit_input_sha256'] or
        ledger['candidate_input_sha256'] != accepted['audit_input_sha256'] or
        ledger['staged_patch_sha256'] != old['main_staged_patch_sha256'] or
        ledger['predecessor_main_acceptance_sha256'] != s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()) or
        ledger['predecessor_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        ledger['isolated_acceptance_sha256'] != s.sha((work / 'ACCEPTANCE.json').read_bytes()) or
        ledger['reviewed_candidate_sha256'] != s.sha((work / 'REVIEW.json').read_bytes()) or
        ledger['integration_driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
        ledger['delta_sha256'] != s.sha((HERE / 'DELTA.patch').read_bytes()) or
        (HERE / 'DELTA.patch').read_text() != source_delta(gate.BASE, work / 'Coq', targets())):
        raise ValueError('installation scope/provenance/driver/delta changed')
    expected = review.baseline_inputs()
    expected.update(installed)
    if s.input_map() != expected or s.index_hash() != ledger['staged_patch_sha256']:
        raise ValueError('installed source/index differs from exact reviewed delta')
    if s.inputs.fingerprint(gate.MAIN, gate.REPO) != ledger['candidate_input_sha256']:
        raise ValueError('installed input differs from accepted candidate')
    actual_main = False
    receipt = HERE / 'MAIN-ACCEPTANCE.json'
    if receipt.exists():
        main = terminal(receipt, 'actual_main_acceptance', ledger['candidate_input_sha256'])
        if (main['installation_sha256'] != s.sha((HERE / 'INSTALLATION.json').read_bytes()) or
            main['driver_sha256'] != s.sha((HERE / 'main-accept.py').read_bytes())):
            raise ValueError('actual-main receipt is not bound to this installation/driver')
        actual_main = True
    return dict(coverage='399/533', staged_patch_preserved=True,
                predecessor_actual_main_acceptance_verified=True,
                source_identical_to_accepted_candidate=True, actual_main_acceptance=actual_main)


if __name__ == '__main__':
    if sys.argv[1:] == ['check']:
        result = check()
    elif len(sys.argv) == 3 and sys.argv[1] in ['plan', 'install']:
        result = (plan if sys.argv[1] == 'plan' else install)(Path(sys.argv[2]).resolve())
        if sys.argv[1] == 'plan':
            result = {n: v for n, v in result.items() if n not in ['before_inputs', 'source_only_delta']}
    else:
        raise ValueError('usage: integration.py plan|install PRIVATE_TREE, or integration.py check')
    print(json.dumps(result, indent=2))
