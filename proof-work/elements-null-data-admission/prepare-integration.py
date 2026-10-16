"""Read-only source-only419 installation planning; never installs or compiles.

Planning requires full isolated419 acceptance and actual-main418 acceptance.
An immutable plan records the exact before/after maps and source delta. It
does not assert that main has been installed or independently accepted419.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('null_data_integration_acceptance', HERE / 'accept.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
g, s = a.g, a.s
prior = g.load('null_data_previous_installation', g.PRED / 'integration.py')


def targets():
    result = g.METADATA + g.SCRIPTS + g.GUARDS + g.NEW_SOURCES
    if (len(g.METADATA + g.SCRIPTS), len(g.GUARDS), len(g.NEW_SOURCES),
        len(result), len(set(result))) != (11, 3, 24, 38, 38):
        raise ValueError('wrong source-only419 target inventory')
    for n in result:
        p = Path(n)
        if (p.is_absolute() or '..' in p.parts or p.suffix in {'.vo', '.vos', '.vok', '.glob'} or
            not p.suffix in {'.v', '.py', '.sh', '.txt', '.tsv', '.expected', '.jets', ''} or
            g.MAIN.resolve() not in (g.MAIN / n).resolve().parents):
            raise ValueError('unsafe/non-source integration target')
    return result


def input_map(work):
    result = {}
    for label, root, suffixes in [
        ('Coq', work / 'Coq', {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}),
        ('C', work / 'C', {'.c', '.h', '.inc', '.S', '.s'}),
        ('Haskell', work / 'Haskell', {'.hs'}),
    ]:
        for p in sorted(root.rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and (
                p.suffix in suffixes or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in'):
                result[label + '/' + str(p.relative_to(root))] = s.sha(p.read_bytes())
    return result


def accepted(work):
    if not (HERE / 'ACCEPTANCE.json').exists() or not (work / 'ACCEPTANCE.json').exists():
        raise ValueError('full isolated419 acceptance required before planning integration')
    reviewed = a.reviewed(work)
    r = json.loads((work / 'ACCEPTANCE.json').read_text())
    launch = json.loads((work / 'AUDIT-RUN.json').read_text())
    terminal = json.loads((work / 'TERMINAL.json').read_text())
    for n in ['ACCEPTANCE.json', 'AUDIT-RUN.json', 'TERMINAL.json']:
        if (work / n).read_bytes() != (HERE / n).read_bytes():
            raise ValueError('audit archive/private receipt differs')
    expected = dict(terminal, full_acceptance=True, coverage='419/533')
    if (r != expected or any(terminal[k] != value for k, value in launch.items()) or
        launch['full_acceptance'] is not False or r['exit_code'] != 0 or
        r['command'] != ['bash', 'check-jets.sh', '--accept'] or r['candidate'] != str(work) or
        r['coverage_before'] != '418/533' or r['coverage_added'] != 1 or
        r['driver_sha256'] != s.sha((HERE / 'accept.py').read_bytes()) or
        r['audit_input_sha256'] != reviewed['candidate_input_sha256'] or
        r['audit_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['review_sha256'] != s.sha((HERE / 'REVIEW.json').read_bytes()) or
        r['source_review_sha256'] != s.sha((g.SOURCE / 'SOURCE-REVIEW.json').read_bytes()) or
        r['predecessor_main_acceptance_sha256'] != s.sha((g.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()) or
        r['staged_patch_sha256'] != s.index_hash() or
        r['log'] != str(work / 'acceptance.log') or
        r['log_sha256'] != s.sha((work / 'acceptance.log').read_bytes()) or
        not (work / 'acceptance.log').read_text().rstrip().endswith(a.MARKER)):
        raise ValueError('full isolated419 terminal/source/review/index evidence differs')
    return r


def plan(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('integration candidate must be a distinct private source tree')
    selected = targets()
    r = accepted(work)
    if prior.check()['actual_main_acceptance'] is not True:
        raise ValueError('actual main418 acceptance required')
    before, index = s.input_map(), s.index_hash()
    if before != g.baseline_inputs() or index != g.PR['staged_patch_sha256']:
        raise ValueError('main/index differs from exact accepted418 checkpoint')
    for n in g.GUARDS + g.NEW_SOURCES:
        if (g.MAIN / n).exists() or (g.MAIN / n).is_symlink():
            raise ValueError('would overwrite an inherited or untracked source: ' + n)
    for n in selected:
        p = work / 'Coq' / n
        if not p.is_file() or p.is_symlink():
            raise ValueError('missing/shared source integration target')
    after = dict(before)
    after.update({'Coq/' + n: s.sha((work / 'Coq' / n).read_bytes()) for n in selected})
    if input_map(work) != after:
        raise ValueError('candidate is not exactly accepted418 plus the source-only delta')
    delta = prior.source_delta(g.MAIN, work / 'Coq', selected)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('planning changed main/index')
    return dict(candidate=str(work), baseline_candidate=str(g.BASE_TREE),
        baseline_input_sha256=g.main_fingerprint(before), candidate_input_sha256=r['audit_input_sha256'],
        coverage_before='418/533', coverage_candidate='419/533', coverage_added=1,
        targets=selected, source_only_targets=38, inherited_proof_overwrites=0, compiler_objects_copied=0,
        before_sha256={'Coq/' + n: before.get('Coq/' + n) for n in selected},
        after_sha256={'Coq/' + n: after['Coq/' + n] for n in selected}, staged_patch_sha256=index,
        source_only_delta_sha256=s.sha(delta.encode()),
        isolated_acceptance_sha256=s.sha((HERE / 'ACCEPTANCE.json').read_bytes()),
        normal_review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((g.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        predecessor_installation_sha256=s.sha((g.PRED / 'INSTALLATION.json').read_bytes()),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['prepare-integration.py', 'test-integration-plan.py', 'accept.py']},
        main_installation=False, full_acceptance=False)


def record(work):
    if (HERE / 'INSTALLATION-PLAN.json').exists():
        raise ValueError('installation plan already recorded; compare it instead')
    r = plan(work)
    g.write(HERE / 'INSTALLATION-PLAN.json', r)
    print('Source-only419 integration plan recorded; main unchanged', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['check', 'record']:
        raise ValueError('usage: prepare-integration.py check|record PRIVATE_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'record':
        record(work)
    else:
        print(json.dumps(plan(work), indent=2))
