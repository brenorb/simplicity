"""Once-only combined418 source integration over actually accepted main415.

Postchecking validates immutable historical receipts, not obsolete predecessor
exact-main checks on a successor. No intermediate unaccepted installation is invented.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRED = HERE.parent / 'elements-issuance-amount-admission'


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


planner = load('combined418_integration_plan', HERE / 'prepare-integration.py')
a, s = planner.a, planner.s
g = a.g
old = load('combined418_prior', PRED / 'integration.py')
read, terminal, source_delta = old.read, old.terminal, old.source_delta
COMMAND, MARKER = old.COMMAND, old.MARKER


def targets():
    configs = [load('combined418_targets_' + prefix, HERE.parent / folder / 'admission.py')
               for folder, _, prefix in a.BATCHES]
    common = configs[0].METADATA + configs[0].SCRIPTS
    if any(c.METADATA + c.SCRIPTS != common for c in configs):
        raise ValueError('metadata/script target scopes differ')
    guards = [n for c in configs for n in c.GUARDS]
    sources = [n for c in configs for n in c.NEW_SOURCES]
    result = common + guards + sources
    if (len(common), len(guards), len(sources), len(result), len(set(result))) != (11, 4, 7, 22, 22):
        raise ValueError('wrong aggregate additive target inventory')
    for n in result:
        p = Path(n)
        if p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'}:
            raise ValueError('unsafe/non-source integration target')
        if g.MAIN.resolve() not in (g.MAIN / n).resolve().parents:
            raise ValueError('integration target escapes main')
    return result


def reviewed_evidence(work):
    """Bind completed historical reviews without requiring current main415."""
    p = read(HERE / 'INSTALLATION-PLAN.json')
    if (p['candidate'] != str(work) or p['coverage_before'] != '415/533' or
        p['coverage_candidate'] != '418/533' or p['coverage_added'] != 3 or
        p['main_installation'] is not False or p['full_acceptance'] is not False or
        p['targets'] != targets() or p['source_only_targets'] != 22 or
        p['inherited_proof_overwrites'] != 0 or p['compiler_objects_copied'] != 0):
        raise ValueError('wrong reviewed plan scope')
    for n, h in p['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('reviewed plan/acceptance tool changed')
    previous, chain = p['baseline_input_sha256'], {}
    for folder, added, prefix in a.BATCHES:
        here = HERE.parent / folder
        v = load('combined418_evidence_' + prefix, here / 'review.py')
        candidate = Path(read(here / 'ASSEMBLY.json')['candidate'])
        r = read(here / 'REVIEW.json')
        if ((candidate / 'REVIEW.json').read_bytes() != (here / 'REVIEW.json').read_bytes() or
            r['full_acceptance'] is not False or r['review']['coverage_added'] != added or
            r['review']['inherited_proof_changes'] != 0 or
            read(candidate / 'ASSEMBLY.json')['predecessor_input_sha256'] != previous or
            r['candidate_input_sha256'] != s.inputs.fingerprint(candidate / 'Coq', candidate) or
            r['preparation_engine_sha256'] != s.sha(v.g.PREPARE_ENGINE.read_bytes()) or
            r['assembly_sha256'] != s.sha((candidate / 'ASSEMBLY.json').read_bytes()) or
            r['preparation_sha256'] != s.sha((candidate / 'PREPARATION.json').read_bytes())):
            raise ValueError('historical source/review chain differs')
        if hasattr(v, 'REVIEW_ENGINE') and r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()):
            raise ValueError('historical review engine changed')
        for n, h in r['tools_sha256'].items():
            if s.sha((here / n).read_bytes()) != h:
                raise ValueError('historical review tool changed')
        for n, h in r['evidence_sha256'].items():
            if s.sha((candidate / n).read_bytes()) != h:
                raise ValueError('historical object/report evidence changed')
        if len(r['checks']) != 6:
            raise ValueError('incomplete historical six-stage review')
        for n, row in r['checks'].items():
            if row['exit_code'] != 0 or row['log_sha256'] != s.sha((candidate / (n + '.log')).read_bytes()):
                raise ValueError('historical review terminal/log differs')
        previous = r['candidate_input_sha256']
        chain[folder] = s.sha((here / 'REVIEW.json').read_bytes())
    if chain != p['review_chain_sha256'] or previous != p['candidate_input_sha256']:
        raise ValueError('review chain differs from verified aggregate plan')
    before = load('combined418_baseline_inputs', HERE.parent / a.BATCHES[0][0] / 'admission.py').baseline_inputs()
    after = dict(before)
    after.update(p['after_sha256'])
    if (planner.input_map(work) != after or
        p['before_sha256'] != {'Coq/' + n: before.get('Coq/' + n) for n in targets()} or
        p['after_sha256'] != {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in targets()}):
        raise ValueError('aggregate candidate is not exact baseline plus planned source delta')
    return p, before, after


def predecessor():
    # Validate the real historical415 installation and actual audit without
    # requiring today's main to still be415 after a successor is installed.
    ledger = read(PRED / 'INSTALLATION.json')
    base_ledger, base_actual = old.predecessor()
    work = Path(ledger['candidate'])
    p, accepted, _, _ = old.candidate_acceptance(work)
    delta = source_delta(Path(p['baseline_candidate']) / 'Coq', work / 'Coq', old.targets())
    expected = dict(candidate=str(work), coverage='415/533', coverage_added=8,
        before_input_sha256=base_actual['audit_input_sha256'], candidate_input_sha256=accepted['audit_input_sha256'],
        staged_patch_sha256=p['staged_patch_sha256'], installed_sha256=p['after_sha256'],
        plan_sha256=s.sha((PRED / 'INSTALLATION-PLAN.json').read_bytes()),
        predecessor_installation_sha256=s.sha((old.PRED / 'INSTALLATION.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((old.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        integration_driver_sha256=s.sha((PRED / 'integration.py').read_bytes()),
        delta_sha256=s.sha(delta.encode()), main_installation=True, actual_main_acceptance=False)
    if (ledger != expected or (PRED / 'DELTA.patch').read_text() != delta or
        p['baseline_input_sha256'] != base_ledger['candidate_input_sha256'] or
        p['baseline_input_sha256'] != base_actual['audit_input_sha256'] or
        p['source_only_delta_sha256'] != s.sha(delta.encode())):
        raise ValueError('historical415 installation/delta/provenance differs')
    actual = terminal(PRED / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', accepted['audit_input_sha256'])
    if (actual['installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        actual['driver_sha256'] != s.sha((PRED / 'main-accept.py').read_bytes())):
        raise ValueError('actual-main415 receipt installation/driver differs')
    return ledger, actual


def candidate_acceptance(work):
    p, before, after = reviewed_evidence(work)
    r = terminal(work / 'ACCEPTANCE.json', 'full_acceptance', p['candidate_input_sha256'])
    if ((work / 'ACCEPTANCE.json').read_bytes() != (HERE / 'ACCEPTANCE.json').read_bytes() or
        r['candidate'] != str(work) or r['coverage'] != '418/533' or r['coverage_before'] != '415/533' or
        r['coverage_added'] != 3 or r['review_chain_sha256'] != p['review_chain_sha256'] or
        r['driver_sha256'] != s.sha((HERE / 'accept.py').read_bytes()) or
        r['baseline_acceptance_sha256'] != s.sha((PRED / 'ACCEPTANCE.json').read_bytes()) or
        r['baseline_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes())):
        raise ValueError('combined418 terminal identity/provenance differs')
    return p, r, before, after


def plan(work):
    current = planner.plan(work)
    if current != read(HERE / 'INSTALLATION-PLAN.json'):
        raise ValueError('current source-only plan differs from recorded plan')
    return current


def install(work):
    if (HERE / 'INSTALLATION.json').exists():
        raise ValueError('combined418 installation already performed')
    pred, actual = predecessor()
    p, accepted, before, after = candidate_acceptance(work)
    if old.check()['actual_main_acceptance'] is not True:
        raise ValueError('actual-main415 must pass before integration')
    plan(work)
    delta = source_delta(g.MAIN, work / 'Coq', targets())
    if s.sha(delta.encode()) != p['source_only_delta_sha256']:
        raise ValueError('planned source delta changed')
    ledger = dict(candidate=str(work), coverage='418/533', coverage_added=3,
        before_input_sha256=actual['audit_input_sha256'], candidate_input_sha256=accepted['audit_input_sha256'],
        staged_patch_sha256=p['staged_patch_sha256'], installed_sha256=p['after_sha256'],
        plan_sha256=s.sha((HERE / 'INSTALLATION-PLAN.json').read_bytes()),
        predecessor_installation_sha256=s.sha((PRED / 'INSTALLATION.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        integration_driver_sha256=s.sha(Path(__file__).read_bytes()),
        delta_sha256=s.sha(delta.encode()), main_installation=True, actual_main_acceptance=False)
    changes = {g.MAIN / n: (work / 'Coq' / n).read_text() for n in targets()}
    changes[HERE / 'DELTA.patch'] = delta
    changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    s.changed(changes)
    if s.input_map() != after or s.index_hash() != p['staged_patch_sha256']:
        raise ValueError('integration changed unrelated source/index')
    return check()


def check():
    ledger = read(HERE / 'INSTALLATION.json')
    work = Path(ledger['candidate'])
    pred, actual = predecessor()
    p, accepted, before, after = candidate_acceptance(work)
    delta = source_delta(Path(p['baseline_candidate']) / 'Coq', work / 'Coq', targets())
    expected = dict(candidate=str(work), coverage='418/533', coverage_added=3,
        before_input_sha256=actual['audit_input_sha256'], candidate_input_sha256=accepted['audit_input_sha256'],
        staged_patch_sha256=p['staged_patch_sha256'], installed_sha256=p['after_sha256'],
        plan_sha256=s.sha((HERE / 'INSTALLATION-PLAN.json').read_bytes()),
        predecessor_installation_sha256=s.sha((PRED / 'INSTALLATION.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        integration_driver_sha256=s.sha(Path(__file__).read_bytes()),
        delta_sha256=s.sha(delta.encode()), main_installation=True, actual_main_acceptance=False)
    if (ledger != expected or (HERE / 'DELTA.patch').read_text() != delta or
        p['baseline_input_sha256'] != pred['candidate_input_sha256'] or
        p['baseline_input_sha256'] != actual['audit_input_sha256'] or
        s.input_map() != after or s.index_hash() != p['staged_patch_sha256'] or
        s.inputs.fingerprint(g.MAIN, g.REPO) != p['candidate_input_sha256']):
        raise ValueError('combined418 installed scope/source/index/provenance differs')
    actual_main = False
    if (HERE / 'MAIN-ACCEPTANCE.json').exists():
        main = terminal(HERE / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', p['candidate_input_sha256'])
        if (main['installation_sha256'] != s.sha((HERE / 'INSTALLATION.json').read_bytes()) or
            main['driver_sha256'] != s.sha((HERE / 'main-accept.py').read_bytes())):
            raise ValueError('actual-main418 receipt binding differs')
        actual_main = True
    return dict(coverage='418/533', staged_patch_preserved=True, predecessor_actual_main_acceptance_verified=True,
        source_identical_to_accepted_candidate=True, actual_main_acceptance=actual_main)


if __name__ == '__main__':
    if sys.argv[1:] == ['check']:
        result = check()
    elif len(sys.argv) == 3 and sys.argv[1] in ['plan', 'install']:
        result = (plan if sys.argv[1] == 'plan' else install)(Path(sys.argv[2]).resolve())
        if sys.argv[1] == 'plan':
            result = {n: v for n, v in result.items() if n not in ['before_sha256', 'after_sha256']}
    else:
        raise ValueError('usage: integration.py plan|install PRIVATE_TREE, or integration.py check')
    print(json.dumps(result, indent=2))
