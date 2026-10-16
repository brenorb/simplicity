"""Once-only full isolated436 acceptance after independent normal review.

The predecessor has real full isolated420 acceptance. Actual-main420 has a
separate audit and must succeed before installation, not be invented here.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('raw436_normal_review', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
COMMAND = ['bash', 'check-jets.sh', '--accept']
MARKER = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'


def reviewed(work):
    r = json.loads((HERE / 'REVIEW.json').read_text())
    if (r != json.loads((work / 'REVIEW.json').read_text()) or
        r['review'] != v.review(work) or r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal436 review scope/identity/source differs')
    for name, digest in r['tools_sha256'].items():
        if s.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('normal436 review tool changed')
    for name, digest in r['evidence_sha256'].items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('normal436 reviewed object/report evidence changed')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
    }
    for folder, stem in [('bitcoin-tapleaf-literal', 'tapleaf'), ('bitcoin-raw-program-source', 'raw-family')]:
        expected[stem + '-source'] = [sys.executable, '-B', folder + '/check-source.py', str(work)]
        expected[stem + '-negative'] = [sys.executable, '-B', folder + '/test-source.py', str(work)]
    if set(r['checks']) != set(expected):
        raise ValueError('incomplete eight-stage independent normal436 review')
    for name, command in expected.items():
        row = r['checks'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / (name + '.log')).read_bytes()) or
            (HERE / (name + '.log')).read_bytes() != (work / (name + '.log')).read_bytes()):
            raise ValueError('normal436 review command/exit/log differs')
    return r


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('isolated436 audit already launched; inspect existing handle/terminal')
    r = reviewed(work)
    before, index = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=COMMAND, audit_input_sha256=fingerprint,
        review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        predecessor_isolated_acceptance_sha256=s.sha((g.PRED / 'ACCEPTANCE.json').read_bytes()),
        predecessor_isolated_input_sha256=g.PRED_ACCEPTED['audit_input_sha256'],
        baseline_main_input_sha256=g.main_fingerprint(before),
        coverage_before='420/533', coverage_added=16, staged_patch_sha256=index,
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log), full_acceptance=False,
        actual_main420_terminal_required_before_install=True, main_installation=False)
    for path in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(path, launch)
    print('Launching full isolated436 acceptance; no main installation or actual-main420 result inferred', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(COMMAND, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for path in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(path, terminal)
    if result.returncode:
        raise ValueError('isolated436 full audit failed; inspect ' + str(log))
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or reviewed(work) != r or
        s.input_map() != before or s.index_hash() != index):
        raise ValueError('incomplete full marker or changed reviewed source/main/index')
    terminal.update(full_acceptance=True, coverage='436/533')
    for path in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(path, terminal)
    s.changed({HERE / 'acceptance.log': log.read_text()})
    print('Isolated436 full acceptance passed; actual-main420 success and guarded integration remain required', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: accept.py PRIVATE_TREE')
    main(Path(sys.argv[1]).resolve())
