"""Guarded source-only combined420 installation and historical postcheck.

Require the real combined full acceptance, never an invented intermediate419
installation. Historical checks do not ask the installed successor to be418.
Do not install while either frozen-baseline audit controller is still alive.
"""
import importlib.util
import json
from pathlib import Path
import shlex
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


planner = load('combined420_installation_plan', HERE / 'prepare-integration.py')
a, s, g = planner.a, planner.s, planner.g
PRED = a.BASELINE
old = planner.prior
read, terminal, source_delta = old.read, old.terminal, old.source_delta
COMMAND, MARKER = old.COMMAND, old.MARKER
targets = planner.targets


def controllers_stopped():
    """A terminal receipt alone can precede its controller's postchecks."""
    names = {str(p / 'accept.py') for p in [g.PRED, HERE]}
    names |= {str(Path(n).relative_to(s.REPO)) for n in list(names)}
    result = subprocess.run(['ps', '-axo', 'command='], check=True,
                            capture_output=True, text=True)
    for line in result.stdout.splitlines():
        try:
            args = shlex.split(line)
        except ValueError:
            args = line.split()
        if names.intersection(args):
            raise ValueError('frozen-baseline audit controller is still running')


def predecessor():
    """Reconstruct actual418 history without an exact-current-main418 check."""
    ledger = read(PRED / 'INSTALLATION.json')
    base_ledger, base_actual = old.predecessor()
    work = Path(ledger['candidate'])
    p, accepted, _, _ = old.candidate_acceptance(work)
    delta = source_delta(Path(p['baseline_candidate']) / 'Coq', work / 'Coq', old.targets())
    expected = dict(candidate=str(work), coverage='418/533', coverage_added=3,
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
        raise ValueError('historical418 installation/delta/provenance differs')
    actual = terminal(PRED / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', accepted['audit_input_sha256'])
    if (actual['installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        actual['driver_sha256'] != s.sha((PRED / 'main-accept.py').read_bytes())):
        raise ValueError('actual-main418 receipt installation/driver differs')
    return ledger, actual


def review_commands(folder, candidate, config):
    stem = 'null-data' if folder == g.PRED else 'lambda'
    args = [str(candidate)] if stem == 'null-data' else ['--repo', str(g.REPO), '--coq', str(candidate / 'Coq')]
    negative = [str(candidate)] if stem == 'null-data' else [str(g.REPO), str(candidate / 'Coq')]
    return {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        stem + '-source': [sys.executable, '-B', config.GUARDS[0]] + args,
        stem + '-negative': [sys.executable, '-B', config.GUARDS[1]] + negative,
        'evidence-tests': [sys.executable, '-B', str(folder / 'test-review.py'), str(candidate)]}


def reviewed_evidence(work):
    p = read(HERE / 'INSTALLATION-PLAN.json')
    if (p['candidate'] != str(work) or p['coverage_before'] != '418/533' or
        p['coverage_candidate'] != '420/533' or p['coverage_added'] != 2 or
        p['targets'] != targets() or p['source_only_targets'] != 66 or
        p['byte_identical_reused_sources'] != g.REUSED_SOURCES or
        p['main_installation'] is not False or p['full_acceptance'] is not False or
        p['inherited_proof_overwrites'] != 0 or p['compiler_objects_copied'] != 0 or
        p['predecessor419_terminal_required'] is not False or
        p['actual_main418_acceptance_required_before_install'] is not True or
        p['full_combined420_acceptance_required_before_install'] is not True):
        raise ValueError('wrong combined420 reviewed plan scope')
    for n, h in p['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('reviewed plan/acceptance tool changed')
    previous, chain = p['baseline_input_sha256'], {}
    for folder, config in [(g.PRED, g.parent), (HERE, g)]:
        v = load('combined420_historical_' + folder.name, folder / 'review.py')
        assembly = read(folder / 'ASSEMBLY.json')
        candidate = Path(assembly['candidate'])
        r = read(folder / 'REVIEW.json')
        if ((candidate / 'REVIEW.json').read_bytes() != (folder / 'REVIEW.json').read_bytes() or
            (candidate / 'ASSEMBLY.json').read_bytes() != (folder / 'ASSEMBLY.json').read_bytes() or
            r['full_acceptance'] is not False or r['review']['coverage_added'] != 1 or
            r['review']['inherited_proof_changes'] != 0 or
            assembly['predecessor_input_sha256'] != previous or
            assembly['staged_patch_sha256'] != p['staged_patch_sha256'] or
            r['candidate_input_sha256'] != s.inputs.fingerprint(candidate / 'Coq', candidate) or
            r['preparation_engine_sha256'] != s.sha(config.PREPARE_ENGINE.read_bytes()) or
            r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
            r['assembly_sha256'] != s.sha((candidate / 'ASSEMBLY.json').read_bytes()) or
            r['preparation_sha256'] != s.sha((candidate / 'PREPARATION.json').read_bytes())):
            raise ValueError('historical420 source/review chain differs')
        for n, h in assembly['proof_evidence_sha256'].items():
            if s.sha((HERE.parent / n).read_bytes()) != h:
                raise ValueError('reviewed proof evidence changed')
        for n, h in r['tools_sha256'].items():
            if s.sha((folder / n).read_bytes()) != h:
                raise ValueError('historical420 review tool changed')
        for n, h in r['evidence_sha256'].items():
            if s.sha((candidate / n).read_bytes()) != h:
                raise ValueError('historical420 object/report evidence changed')
        expected = review_commands(folder, candidate, config)
        if set(r['checks']) != set(expected):
            raise ValueError('incomplete historical420 six-stage review')
        for n, command in expected.items():
            row = r['checks'][n]
            if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((candidate / (n + '.log')).read_bytes())):
                raise ValueError('historical420 review command/exit/log differs')
        previous = r['candidate_input_sha256']
        chain[folder.name] = s.sha((folder / 'REVIEW.json').read_bytes())
    if previous != p['candidate_input_sha256'] or chain != p['review_chain_sha256']:
        raise ValueError('review chain differs from combined420 plan')
    before = dict(g.PRED_META['baseline_inputs'])
    after = dict(before)
    after.update(p['after_sha256'])
    baseline_tree = Path(p['baseline_candidate'])
    if (planner.input_map(baseline_tree) != before or planner.input_map(work) != after or
        p['before_sha256'] != {'Coq/' + n: before.get('Coq/' + n) for n in targets()} or
        p['after_sha256'] != {'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in targets()}):
        raise ValueError('candidate is not exact accepted418 plus planned sources')
    for n in g.REUSED_SOURCES:
        if (baseline_tree / 'Coq' / n).read_bytes() != (work / 'Coq' / n).read_bytes():
            raise ValueError('reused source differs from historical418')
    return p, before, after


def candidate_acceptance(work):
    # Fail cheaply before historical rehashes; review is not full acceptance.
    if not (HERE / 'ACCEPTANCE.json').is_file() or not (work / 'ACCEPTANCE.json').is_file():
        raise ValueError('real full combined420 terminal acceptance is required')
    p, before, after = reviewed_evidence(work)
    r = terminal(work / 'ACCEPTANCE.json', 'full_acceptance', p['candidate_input_sha256'])
    launch = read(HERE / 'AUDIT-RUN.json')
    t = read(HERE / 'TERMINAL.json')
    if ((work / 'ACCEPTANCE.json').read_bytes() != (HERE / 'ACCEPTANCE.json').read_bytes() or
        (work / 'TERMINAL.json').read_bytes() != (HERE / 'TERMINAL.json').read_bytes() or
        (work / 'AUDIT-RUN.json').read_bytes() != (HERE / 'AUDIT-RUN.json').read_bytes() or
        r != dict(t, full_acceptance=True, coverage='420/533') or
        {n: r[n] for n in launch} != dict(launch, full_acceptance=True) or
        r['candidate'] != str(work) or r['coverage'] != '420/533' or
        r['coverage_before'] != '418/533' or r['coverage_added'] != 2 or
        r['predecessor_isolated_acceptance_required'] is not False or
        r['review_chain_sha256'] != p['review_chain_sha256'] or
        r['staged_patch_sha256'] != p['staged_patch_sha256'] or
        r['driver_sha256'] != s.sha((HERE / 'accept.py').read_bytes()) or
        r['baseline_main_acceptance_sha256'] != p['baseline_main_acceptance_sha256'] or
        r['baseline_installation_sha256'] != p['baseline_installation_sha256']):
        raise ValueError('combined420 terminal identity/provenance differs')
    return p, r, before, after


def expected_ledger(work, p, accepted, actual, delta):
    return dict(candidate=str(work), coverage='420/533', coverage_added=2,
        before_input_sha256=actual['audit_input_sha256'], candidate_input_sha256=accepted['audit_input_sha256'],
        staged_patch_sha256=p['staged_patch_sha256'], installed_sha256=p['after_sha256'],
        plan_sha256=s.sha((HERE / 'INSTALLATION-PLAN.json').read_bytes()),
        predecessor_installation_sha256=s.sha((PRED / 'INSTALLATION.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated_acceptance_sha256=s.sha((work / 'ACCEPTANCE.json').read_bytes()),
        integration_driver_sha256=s.sha(Path(__file__).read_bytes()),
        delta_sha256=s.sha(delta.encode()), main_installation=True, actual_main_acceptance=False)


def install(work):
    if (HERE / 'INSTALLATION.json').exists():
        raise ValueError('combined420 installation already performed')
    p, accepted, before, after = candidate_acceptance(work)
    controllers_stopped()
    pred, actual = predecessor()
    a.baseline()
    if planner.plan(work) != p:
        raise ValueError('current combined420 source plan differs from recorded plan')
    delta = source_delta(g.MAIN, work / 'Coq', targets())
    if s.sha(delta.encode()) != p['source_only_delta_sha256']:
        raise ValueError('planned combined420 source delta changed')
    # All validation precedes the first write. No inherited proof or object is copied.
    ledger = expected_ledger(work, p, accepted, actual, delta)
    changes = {g.MAIN / n: (work / 'Coq' / n).read_text() for n in targets()}
    changes[HERE / 'DELTA.patch'] = delta
    changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    changes[HERE / 'acceptance.log'] = Path(accepted['log']).read_text()
    s.changed(changes)
    if s.input_map() != after or s.index_hash() != p['staged_patch_sha256']:
        raise ValueError('combined420 integration changed unrelated sources/index')
    return check()


def check():
    ledger = read(HERE / 'INSTALLATION.json')
    work = Path(ledger['candidate'])
    pred, actual = predecessor()
    p, accepted, before, after = candidate_acceptance(work)
    delta = source_delta(Path(p['baseline_candidate']) / 'Coq', work / 'Coq', targets())
    if (ledger != expected_ledger(work, p, accepted, actual, delta) or
        (HERE / 'DELTA.patch').read_text() != delta or
        s.sha(delta.encode()) != p['source_only_delta_sha256'] or
        p['baseline_input_sha256'] != pred['candidate_input_sha256'] or
        p['baseline_input_sha256'] != actual['audit_input_sha256'] or
        p['baseline_main_acceptance_sha256'] != s.sha((PRED / 'MAIN-ACCEPTANCE.json').read_bytes()) or
        p['baseline_installation_sha256'] != s.sha((PRED / 'INSTALLATION.json').read_bytes()) or
        (HERE / 'acceptance.log').read_bytes() != Path(accepted['log']).read_bytes() or
        s.input_map() != after or s.index_hash() != p['staged_patch_sha256'] or
        s.inputs.fingerprint(g.MAIN, g.REPO) != p['candidate_input_sha256']):
        raise ValueError('combined420 installed source/index/provenance differs')
    actual_main = False
    if (HERE / 'MAIN-ACCEPTANCE.json').exists():
        main = terminal(HERE / 'MAIN-ACCEPTANCE.json', 'actual_main_acceptance', p['candidate_input_sha256'])
        if (main['installation_sha256'] != s.sha((HERE / 'INSTALLATION.json').read_bytes()) or
            main['driver_sha256'] != s.sha((HERE / 'main-accept.py').read_bytes())):
            raise ValueError('actual-main420 receipt binding differs')
        actual_main = True
    return dict(coverage='420/533', staged_patch_preserved=True,
        predecessor_actual_main_acceptance_verified=True,
        source_identical_to_accepted_candidate=True, actual_main_acceptance=actual_main)


if __name__ == '__main__':
    if sys.argv[1:] == ['check']:
        result = check()
    elif len(sys.argv) == 3 and sys.argv[1] == 'install':
        result = install(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: integration.py install PRIVATE_TREE, or integration.py check')
    print(json.dumps(result, indent=2))
