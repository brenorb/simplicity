"""Guarded additive 402 integration after real isolated and actual-main audits.

Planning is read-only and can run during the audits. Installation cannot: it
requires both successful terminal receipts, not launch records or preparation.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRED = HERE.parent / 'elements-tap-getters-admission'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


review = load('lbtc_integration_review', HERE / 'review.py')
old = load('lbtc_integration_prior', PRED / 'integration.py')
g, s = review.g, review.s
read, terminal, source_delta = old.read, old.terminal, old.source_delta
COMMAND, MARKER = old.COMMAND, old.MARKER


def targets():
    result = g.METADATA + g.SCRIPTS + g.GUARDS + g.NEW_SOURCES
    if (len(result) != 16 or len(set(result)) != 16 or
        tuple(map(len, [g.METADATA, g.SCRIPTS, g.GUARDS, g.NEW_SOURCES])) != (7, 4, 2, 3)):
        raise ValueError('unexpected additive source delta')
    for n in result:
        p = Path(n)
        if p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'}:
            raise ValueError('unsafe/non-source target')
        if g.MAIN.resolve() not in (g.MAIN / p).resolve().parents:
            raise ValueError('target escapes main source tree')
    return result


def reviewed_evidence(work):
    r = read(work / 'REVIEW.json')
    if (r['full_acceptance'] is not False or r['review']['coverage_added'] != 1 or
        r['review']['inherited_proof_changes'] != 0 or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes())):
        raise ValueError('wrong reviewed additive scope or review promoted to acceptance')
    for n, h in r['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('reviewed tool drift')
    for n, h in r['evidence_sha256'].items():
        if s.sha((work / n).read_bytes()) != h:
            raise ValueError('reviewed source/object/log drift')
    if s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256']:
        raise ValueError('reviewed candidate source changed')
    return r


def predecessor():
    ledger = read(PRED / 'INSTALLATION.json')
    old.predecessor()
    old.candidate_acceptance(Path(ledger['candidate']))
    if (ledger['coverage'] != '401/533' or ledger['coverage_added'] != 2 or
        ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
        ledger['candidate_input_sha256'] != g.PRED_REVIEW['candidate_input_sha256']):
        raise ValueError('wrong historical 401 installation')
    actual = terminal(PRED / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', ledger['candidate_input_sha256'])
    if (actual['installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        actual['driver_sha256'] != s.sha((PRED / 'main-accept.py').read_bytes()) or
        ledger['integration_driver_sha256'] != s.sha((PRED / 'integration.py').read_bytes())):
        raise ValueError('predecessor actual-main/installation/driver binding differs')
    return ledger, actual


def candidate_acceptance(work):
    r = reviewed_evidence(work)
    a = terminal(work / 'ACCEPTANCE.json', 'full_acceptance', r['candidate_input_sha256'])
    if (a['coverage'] != '402/533' or a['candidate'] != str(work) or
        a['review_sha256'] != s.sha((work / 'REVIEW.json').read_bytes()) or
        a['driver_sha256'] != s.sha((HERE / 'accept.py').read_bytes()) or
        a['predecessor_acceptance_sha256'] != s.sha((PRED / 'ACCEPTANCE.json').read_bytes()) or
        a['predecessor_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        (work / 'ACCEPTANCE.json').read_bytes() != (HERE / 'ACCEPTANCE.json').read_bytes()):
        raise ValueError('402 acceptance identity/provenance differs')
    return r, a


def plan(work):
    review.review(work)
    reviewed_evidence(work)
    meta = read(work / 'ASSEMBLY.json')
    before = g.baseline_inputs()
    if s.input_map() != before or s.index_hash() != meta['staged_patch_sha256']:
        raise ValueError('main/index is not the exact 401 baseline')
    for n in g.NEW_SOURCES + g.GUARDS:
        if (g.MAIN / n).exists():
            raise ValueError('additive source/guard already exists')
    paths = targets()
    delta = source_delta(g.MAIN, work / 'Coq', paths)
    if delta != source_delta(g.BASE, work / 'Coq', paths):
        raise ValueError('source delta does not start from exact predecessor')
    return dict(candidate=str(work), before_inputs=before, targets=paths,
        installed_sha256={'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in paths},
        staged_patch_sha256=meta['staged_patch_sha256'], before_input_sha256=meta['predecessor_input_sha256'],
        candidate_input_sha256=read(work / 'REVIEW.json')['candidate_input_sha256'],
        source_only_delta=delta, coverage='402/533', coverage_added=1,
        main_installation=False, actual_main_acceptance=False)


def install(work):
    if (HERE / 'INSTALLATION.json').exists():
        raise ValueError('one-time 402 installation already performed')
    predecessor()
    _, accepted = candidate_acceptance(work)
    if old.check()['actual_main_acceptance'] is not True:
        raise ValueError('401 actual-main acceptance must finish before installation')
    p = plan(work)
    if p['candidate_input_sha256'] != accepted['audit_input_sha256']:
        raise ValueError('planned and accepted inputs differ')
    ledger = {n: p[n] for n in ['candidate', 'installed_sha256', 'staged_patch_sha256',
        'before_input_sha256', 'candidate_input_sha256', 'coverage', 'coverage_added']}
    ledger.update(main_installation=True, actual_main_acceptance=False,
        predecessor_main_acceptance_sha256=s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        predecessor_installation_sha256=s.sha((PRED / 'INSTALLATION.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        reviewed_candidate_sha256=s.sha((work / 'REVIEW.json').read_bytes()),
        integration_driver_sha256=s.sha(Path(__file__).read_bytes()), delta_sha256=s.sha(p['source_only_delta'].encode()))
    changes = {g.MAIN / n: (work / 'Coq' / n).read_text() for n in p['targets']}
    changes[HERE / 'DELTA.patch'] = p['source_only_delta']
    changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    s.changed(changes)
    expected = dict(p['before_inputs'])
    expected.update(p['installed_sha256'])
    if s.input_map() != expected or s.index_hash() != p['staged_patch_sha256']:
        raise ValueError('installation changed unrelated source/index')
    return check()


def check():
    ledger = read(HERE / 'INSTALLATION.json')
    work = Path(ledger['candidate'])
    pred, actual = predecessor()
    _, accepted = candidate_acceptance(work)
    installed = {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in targets()}
    if (ledger['coverage'] != '402/533' or ledger['coverage_added'] != 1 or
        ledger['main_installation'] is not True or ledger['actual_main_acceptance'] is not False or
        ledger['installed_sha256'] != installed or
        ledger['before_input_sha256'] != pred['candidate_input_sha256'] or
        ledger['before_input_sha256'] != actual['audit_input_sha256'] or
        ledger['candidate_input_sha256'] != accepted['audit_input_sha256'] or
        ledger['staged_patch_sha256'] != pred['staged_patch_sha256'] or
        ledger['predecessor_main_acceptance_sha256'] != s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()) or
        ledger['predecessor_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        ledger['isolated_acceptance_sha256'] != s.sha((work / 'ACCEPTANCE.json').read_bytes()) or
        ledger['reviewed_candidate_sha256'] != s.sha((work / 'REVIEW.json').read_bytes()) or
        ledger['integration_driver_sha256'] != s.sha(Path(__file__).read_bytes()) or
        ledger['delta_sha256'] != s.sha((HERE / 'DELTA.patch').read_bytes()) or
        (HERE / 'DELTA.patch').read_text() != source_delta(g.BASE, work / 'Coq', targets())):
        raise ValueError('402 installation scope/provenance/delta differs')
    expected = dict(g.baseline_inputs())
    expected.update(installed)
    if s.input_map() != expected or s.index_hash() != ledger['staged_patch_sha256']:
        raise ValueError('installed main/source/index differs')
    if s.inputs.fingerprint(g.MAIN, g.REPO) != ledger['candidate_input_sha256']:
        raise ValueError('main is not source-identical to accepted 402 candidate')
    actual_main = False
    receipt = HERE / 'MAIN-ACCEPTANCE.json'
    if receipt.exists():
        main = terminal(receipt, 'actual_main_acceptance', ledger['candidate_input_sha256'])
        if (main['installation_sha256'] != s.sha((HERE / 'INSTALLATION.json').read_bytes()) or
            main['driver_sha256'] != s.sha((HERE / 'main-accept.py').read_bytes())):
            raise ValueError('actual-main receipt installation/driver differs')
        actual_main = True
    return dict(coverage='402/533', staged_patch_preserved=True,
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
