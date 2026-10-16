"""Once-only combined full467 audit after real447 and both reviewed deltas.

The two-jet449 delta is included, not given a fabricated acceptance receipt.
The command audits the complete467 union, including all inherited gates and
the full nine-module SHA startup dependency closure. No main installation.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('normal467_combined_accept_review', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
prior = g.prior
COMMAND, MARKER = prior.COMMAND, prior.MARKER
ROOT447_FOLDER, ROOT447_TREE = g.parent.PRED, g.parent.BASE_TREE


def reviewed(work):
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('normal467 completed independent review required; inspect its existing controller')
    r = json.loads((HERE / 'REVIEW.json').read_text())
    if (r != json.loads((work / 'REVIEW.json').read_text()) or r['review'] != v.review(work) or
        r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal467 reviewed source/identity/scope differs')
    names = ['admission.py', 'coverage-boundary.py', 'coverage-fixtures.py', 'review.py', 'test-review.py']
    if r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in names}:
        raise ValueError('normal467 reviewed tools changed')
    actual = {str(p.relative_to(work)): s.sha(p.read_bytes()) for p in work.rglob('*')
              if p.is_file() and p.suffix in ['.log', '.vo'] and p != work / 'acceptance.log'}
    if r['evidence_sha256'] != actual:
        raise ValueError('normal467 reviewed evidence/object inventory differs')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
    }
    for folder in g.SOURCE_FOLDERS:
        for kind, script in [('positive', 'check-source.py'), ('negative', 'test-source.py')]:
            expected[folder + '-' + kind] = [sys.executable, '-B', folder + '/' + script, str(work)]
    if len(expected) != 6 or set(r['checks']) != set(expected):
        raise ValueError('incomplete normal467 six-stage review')
    for name, cmd in expected.items():
        log = work / (name + '.log')
        if (r['checks'][name] != dict(command=cmd, exit_code=0, log_sha256=s.sha(log.read_bytes())) or
            (HERE / log.name).read_bytes() != log.read_bytes()):
            raise ValueError('normal467 reviewed command/exit/log differs')
    return r


def predecessor447():
    # The existing exact validator checks both real receipt/log copies, the
    # command/exit/driver, every earlier full-audit prerequisite, final marker,
    # current immutable source fingerprint and all recorded review evidence.
    return prior.predecessor447()


def prerequisites(work):
    if not (ROOT447_FOLDER / 'ACCEPTANCE.json').is_file():
        raise ValueError('real successful full447 terminal required')
    if not (HERE / 'REVIEW.json').is_file():
        raise ValueError('normal467 completed independent review required')
    accepted = predecessor447()
    middle = prior.reviewed(g.BASE_TREE)
    current = reviewed(work)
    if (accepted['coverage'] != '447/533' or accepted['full_acceptance'] is not True or
        middle['full_acceptance'] is not False or middle['review']['coverage_added'] != 2 or
        current['full_acceptance'] is not False or current['review']['coverage_added'] != 18):
        raise ValueError('combined447-plus-two-plus-eighteen scope differs')
    return dict(actual_main420_acceptance_sha256=s.sha((HERE.parent / 'scalar-lambda-admission/MAIN-ACCEPTANCE.json').read_bytes()),
        isolated447_acceptance_sha256=s.sha((ROOT447_FOLDER / 'ACCEPTANCE.json').read_bytes()),
        isolated447_input_sha256=accepted['audit_input_sha256'],
        reviewed449_delta_sha256=s.sha((g.PRED / 'REVIEW.json').read_bytes()),
        reviewed449_input_sha256=middle['candidate_input_sha256'],
        normal467_review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        normal467_input_sha256=current['candidate_input_sha256'],
        full449_acceptance_claimed=False, combined_delta_jets=20)


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('combined full467 already launched; inspect its existing handle/terminal')
    chain = prerequisites(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=COMMAND, audit_input_sha256=fingerprint,
        baseline_main_input_sha256=g.main_fingerprint(before), staged_patch_sha256=index,
        coverage_before='420/533', coverage_added=47, review_chain=chain,
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log),
        full_acceptance=False, main_installation=False)
    for path in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(path, launch)
    print('Launching combined full467 after real447 acceptance and both reviewed deltas; main stays420', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(COMMAND, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for path in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(path, terminal)
    if result.returncode:
        raise ValueError('combined full467 failed; inspect ' + str(log))
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or
        prerequisites(work) != chain or s.input_map() != before or s.index_hash() != index):
        raise ValueError('combined full467 final marker/evidence/source/main/index differs')
    terminal.update(full_acceptance=True, coverage='467/533')
    for path in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(path, terminal)
    s.changed({HERE / 'acceptance.log': log.read_text()})
    print('Combined full467 acceptance passed; guarded source-only main integration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: accept.py COMBINED_TREE')
    main(Path(sys.argv[1]).resolve())
