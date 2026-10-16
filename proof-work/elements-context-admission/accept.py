"""Once-only full447 acceptance, requiring real443 success and reviewed delta.

This controller never installs main or treats preparation as acceptance.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal447_accept_review', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
prior = g.prior
COMMAND, MARKER = prior.COMMAND, prior.MARKER


def predecessor443():
    folder, work = g.PRED, g.BASE_TREE
    for name in ['AUDIT-RUN.json', 'TERMINAL.json', 'ACCEPTANCE.json', 'acceptance.log']:
        if not (folder / name).is_file():
            raise ValueError('real successful full443 terminal required; inspect its existing controller')
        if (folder / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('full443 terminal/log copies differ')
    launch, terminal, accepted = [json.loads((folder / name).read_text()) for name in
                                  ['AUDIT-RUN.json', 'TERMINAL.json', 'ACCEPTANCE.json']]
    expected = dict(candidate=str(work), command=COMMAND,
        audit_input_sha256=g.PRED_REVIEW['candidate_input_sha256'],
        baseline_main_input_sha256=g.main_fingerprint(s.input_map()), staged_patch_sha256=s.index_hash(),
        coverage_before='420/533', coverage_added=23, review_chain=prior.prerequisites(work),
        driver_sha256=s.sha((folder / 'accept.py').read_bytes()), log=str(work / 'acceptance.log'),
        full_acceptance=False, main_installation=False)
    if (launch != expected or
        terminal != dict(launch, exit_code=0, seconds=terminal['seconds'],
                         log_sha256=s.sha((work / 'acceptance.log').read_bytes())) or
        not isinstance(terminal['seconds'], (int, float)) or terminal['seconds'] <= 0 or
        accepted != dict(terminal, full_acceptance=True, coverage='443/533') or
        not (work / 'acceptance.log').read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != accepted['audit_input_sha256']):
        raise ValueError('full443 successful terminal identity/scope/provenance differs')
    return accepted


def reviewed(work):
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('normal447 recorded independent review required; poll its existing controller')
    r = json.loads((HERE / 'REVIEW.json').read_text())
    if (r != json.loads((work / 'REVIEW.json').read_text()) or r['review'] != v.review(work) or
        r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal447 reviewed source/identity/scope differs')
    expected_tools = ['admission.py', 'coverage-boundary.py', 'coverage-fixtures.py', 'review.py', 'test-review.py']
    if r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in expected_tools}:
        raise ValueError('normal447 reviewed tools changed')
    actual = {str(p.relative_to(work)): s.sha(p.read_bytes()) for p in work.rglob('*')
              if p.is_file() and p.suffix in ['.log', '.vo'] and p != work / 'acceptance.log'}
    if r['evidence_sha256'] != actual:
        raise ValueError('normal447 reviewed evidence/object inventory differs')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
    }
    for folder in g.SOURCE_FOLDERS:
        for kind, script in [('positive', 'check-source.py'), ('negative', 'test-source.py')]:
            expected[folder + '-' + kind] = [sys.executable, '-B', folder + '/' + script, str(work)]
    if len(expected) != 12 or set(r['checks']) != set(expected):
        raise ValueError('incomplete normal447 twelve-stage review')
    for name, command in expected.items():
        log = work / (name + '.log')
        if (r['checks'][name] != dict(command=command, exit_code=0, log_sha256=s.sha(log.read_bytes())) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('normal447 reviewed command/exit/log differs')
    return r


def prerequisites(work):
    # Fail before expensive rehashing while either real terminal is pending.
    if not (g.PRED / 'ACCEPTANCE.json').is_file():
        raise ValueError('real successful full443 terminal required; inspect its existing controller')
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('normal447 recorded independent review required; poll its existing controller')
    predecessor, review = predecessor443(), reviewed(work)
    return dict(actual_main420_acceptance_sha256=s.sha((g.parent.parent.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated443_acceptance_sha256=s.sha((g.PRED / 'ACCEPTANCE.json').read_bytes()),
        isolated443_input_sha256=predecessor['audit_input_sha256'],
        normal447_review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        normal447_input_sha256=review['candidate_input_sha256'])


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('full447 audit already launched; inspect its existing handle/terminal')
    chain = prerequisites(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=COMMAND, audit_input_sha256=fingerprint,
        baseline_main_input_sha256=g.main_fingerprint(before), staged_patch_sha256=index,
        coverage_before='420/533', coverage_added=27, review_chain=chain,
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log),
        full_acceptance=False, main_installation=False)
    for path in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(path, launch)
    print('Launching full isolated447 after real443 acceptance and twelve-stage delta review; main stays420', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(COMMAND, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for path in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(path, terminal)
    if result.returncode:
        raise ValueError('full447 audit failed; inspect ' + str(log))
    # acceptance.log is created by this phase, not part of the prior review.
    # Other bound source/evidence remains immutable; validate it independently.
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or
        prerequisites(work) != chain or s.input_map() != before or s.index_hash() != index):
        raise ValueError('full447 final marker missing or reviewed evidence/main/index changed')
    terminal.update(full_acceptance=True, coverage='447/533')
    for path in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(path, terminal)
    s.changed({HERE / 'acceptance.log': log.read_text()})
    print('Isolated447 full acceptance passed; guarded source-only main integration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: accept.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
