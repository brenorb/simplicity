"""Independent source/object/command/type/axiom review of the shared lift."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('application_lift_checked', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review(work):
    prior, base = g.tree(work)
    r = json.loads((HERE / 'CHECKED.json').read_text())
    launch = json.loads((HERE / 'RUN.json').read_text())
    if (r['candidate'] != str(work) or r['base_candidate'] != str(base) or
        r['base_receipt_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        r['base_input_sha256'] != prior['candidate_input_sha256'] or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('source/checkpoint/tool/index identity differs')
    if (r['modules'] != g.MODULES or r['new_sources'] != g.NEW_SOURCES or r['results'] != g.RESULTS or
        r['definitions'] or r['recursive_kernel_check'] is not True or launch['recursive_kernel_check'] is not False or
        r['shared_lift_proved'] is not True or r['concrete_jet_examples'] != 2 or
        r['requires_nonempty_output'] is not True or r['coverage_added'] != 0 or
        any(r[k] is not False for k in ['normal_registration', 'full_acceptance'])):
        raise ValueError('wrong proof/registration scope')
    for k, value in launch.items():
        if k not in ['commands', 'recursive_kernel_check'] and r[k] != value:
            raise ValueError('launch/terminal identity differs')
    for table, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[table]) != set(g.MODULES):
            raise ValueError('wrong fresh source/object inventory')
        for m, h in r[table].items():
            p = work / 'Coq' / (m.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != h:
                raise ValueError('fresh source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.MODULES}
    for suffix in ['assumptions', 'contracts']:
        commands['application-context-lift-' + suffix] = ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('application_context_lift_' + suffix + '.v'))]
    commands['kernel'] = g.KERNEL_COMMAND
    if set(r['commands']) != set(commands) or set(launch['commands']) != set(commands) - {'kernel'}:
        raise ValueError('incomplete fresh command inventory')
    for n, expected in commands.items():
        row, log = r['commands'][n], work / (n + '.log')
        if (row['command'] != expected or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            n in launch['commands'] and launch['commands'][n] != row):
            raise ValueError('fresh command/exit/log differs')
    report = (work / 'application-context-lift-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) != [('TYPE', n) for n in g.RESULTS]):
        raise ValueError('truncated/incomplete full type report')
    deps = s.reports.assumptions((work / 'application-context-lift-assumptions.log').read_text())
    if deps != {n: s.SIX for n in g.RESULTS} or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()}:
        raise ValueError('unexpected theorem assumptions')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    return dict(candidate=str(work), results=3, definitions=0, concrete_c_to_spec_examples=2,
        shared_nonempty_output_lift=True, full_bitmachine_frame_preservation=True,
        inherited_source_changes=0, recursive_kernel_check=True, new_assumptions=0,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('review already recorded')
    result = review(work)
    commands = {'evidence-tests': s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 600)}
    if review(work) != result:
        raise ValueError('review changed during tests')
    r = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        launch_sha256=s.sha((HERE / 'RUN.json').read_bytes()), commands=commands,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'review.py', 'test-review.py']},
        normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(r, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Shared lift and two concrete examples independently reviewed; no added coverage', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
