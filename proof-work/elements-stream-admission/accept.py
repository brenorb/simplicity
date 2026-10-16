"""Once-only full normal443 audit, gated by real predecessor terminals.

Preparation/source review are not full acceptance. Require actual-main420 and
isolated436 success, unchanged evidence and exact original stage before launch.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal443_reviewed_acceptance', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
old = g.parent.parent
COMMAND, MARKER = old.COMMAND, old.MARKER


def reviewed(work):
    r = old.read(HERE / 'REVIEW.json')
    if (r != old.read(work / 'REVIEW.json') or r['review'] != v.review(work) or
        r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal443 review identity/source/scope differs')
    for name, digest in r['tools_sha256'].items():
        if s.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('normal443 reviewed tool changed')
    for name, digest in r['evidence_sha256'].items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('normal443 reviewed object/report changed')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'stream-source': [sys.executable, '-B', g.GUARDS[0], str(work)],
        'stream-negative': [sys.executable, '-B', g.GUARDS[1], str(work)],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
    }
    if set(r['checks']) != set(expected):
        raise ValueError('incomplete normal443 six-stage review')
    for name, command in expected.items():
        row = r['checks'][name]
        log = work / (name + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('normal443 review command/exit/log differs')
    return r


def predecessor436():
    folder, work = g.PRED, g.BASE_TREE
    if not (folder / 'ACCEPTANCE.json').is_file():
        raise ValueError('real successful isolated436 full acceptance is required; poll its existing controller')
    for name in ['AUDIT-RUN.json', 'TERMINAL.json', 'ACCEPTANCE.json']:
        if (folder / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('isolated436 terminal copies differ')
    r = old.terminal(folder / 'ACCEPTANCE.json', 'full_acceptance', g.PRED_REVIEW['candidate_input_sha256'])
    launch, terminal = old.read(folder / 'AUDIT-RUN.json'), old.read(folder / 'TERMINAL.json')
    expected = dict(candidate=str(work), command=COMMAND,
        audit_input_sha256=g.PRED_REVIEW['candidate_input_sha256'],
        review_sha256=s.sha((folder / 'REVIEW.json').read_bytes()),
        predecessor_isolated_acceptance_sha256=s.sha((g.parent.PRED / 'ACCEPTANCE.json').read_bytes()),
        predecessor_isolated_input_sha256=g.parent.PRED_ACCEPTED['audit_input_sha256'],
        baseline_main_input_sha256=g.main_fingerprint(s.input_map()), coverage_before='420/533',
        coverage_added=16, staged_patch_sha256=s.index_hash(),
        driver_sha256=s.sha((folder / 'accept.py').read_bytes()), log=str(work / 'acceptance.log'),
        full_acceptance=False, actual_main420_terminal_required_before_install=True, main_installation=False)
    if (launch != expected or r != dict(terminal, full_acceptance=True, coverage='436/533') or
        {n: terminal[n] for n in launch} != launch or terminal['exit_code'] != 0 or
        terminal['seconds'] <= 0 or terminal['log_sha256'] != r['log_sha256'] or
        (folder / 'acceptance.log').read_bytes() != (work / 'acceptance.log').read_bytes() or
        g.prior.reviewed(work) != g.PRED_REVIEW):
        raise ValueError('isolated436 full terminal identity/provenance differs')
    return r


def prerequisites(work):
    # Fail early on pending terminals rather than doing costly review rehashes.
    if not (g.PRED / 'ACCEPTANCE.json').is_file():
        raise ValueError('real successful isolated436 full acceptance is required; poll its existing controller')
    if not (g.parent.PRED / 'MAIN-ACCEPTANCE.json').is_file():
        raise ValueError('real actual-main420 full acceptance is required')
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('normal443 independent review is not complete; poll its existing controller')
    main = old.check()
    if main['actual_main_acceptance'] is not True or main['coverage'] != '420/533':
        raise ValueError('actual main is not fully accepted420')
    pred, review = predecessor436(), reviewed(work)
    return dict(actual_main420_acceptance_sha256=s.sha((g.parent.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        isolated436_acceptance_sha256=s.sha((g.PRED / 'ACCEPTANCE.json').read_bytes()),
        isolated436_input_sha256=pred['audit_input_sha256'],
        normal443_review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        normal443_input_sha256=review['candidate_input_sha256'])


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('normal443 audit already launched; inspect its existing handle/terminal')
    chain = prerequisites(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=COMMAND, audit_input_sha256=fingerprint,
        baseline_main_input_sha256=g.main_fingerprint(before), staged_patch_sha256=index,
        coverage_before='420/533', coverage_added=23, review_chain=chain,
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log),
        full_acceptance=False, main_installation=False)
    for path in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(path, launch)
    print('Launching full isolated443 audit after real main420/isolated436 success; main stays420', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(COMMAND, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for path in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(path, terminal)
    if result.returncode:
        raise ValueError('isolated443 full audit failed; inspect ' + str(log))
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or prerequisites(work) != chain or
        s.input_map() != before or s.index_hash() != index):
        raise ValueError('normal443 final marker missing or reviewed evidence/main/index changed')
    terminal.update(full_acceptance=True, coverage='443/533')
    for path in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(path, terminal)
    s.changed({HERE / 'acceptance.log': log.read_text()})
    print('Isolated443 full acceptance passed; guarded source-only main integration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: accept.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
