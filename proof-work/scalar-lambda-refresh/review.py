"""Independent review of refreshed initialized-lambda source and evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_refreshed_check', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review(work):
    baseline = g.tree(work)
    assembly = json.loads((HERE / 'ASSEMBLY.json').read_text())
    r = json.loads((HERE / 'CHECKED.json').read_text())
    launch = json.loads((HERE / 'RUN.json').read_text())
    if (assembly['candidate'] != str(work) or r['candidate'] != str(work) or
        assembly['baseline'] != str(g.BASE_TREE) or
        assembly['baseline_input_sha256'] != baseline['audit_input_sha256'] or
        assembly['baseline_main_acceptance_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        assembly['old_assembly_sha256'] != s.sha((g.OLD / 'ASSEMBLY.json').read_bytes()) or
        r['assembly_sha256'] != s.sha((HERE / 'ASSEMBLY.json').read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        any(x['main_inputs'] != s.input_map() or x['staged_patch_sha256'] != s.index_hash() for x in [assembly, r]) or
        any(x['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} for x in [assembly, r])):
        raise ValueError('source/assembly/checkpoint/tool/index differs')
    if (r['modules'] != g.MODULES or r['fresh_modules'] != g.MODULES or
        assembly['modules'] != g.MODULES or assembly['new_sources'] != g.NEW_SOURCES or assembly['reused_sources'] != g.REUSED or
        r['recursive_kernel_check'] is not True or launch['recursive_kernel_check'] is not False or
        r['canonical_source_guard'] is not True or launch['canonical_source_guard'] is not False or
        any(x['coverage_added'] != 0 or x['normal_registration'] is not False or x['full_acceptance'] is not False for x in [assembly, r])):
        raise ValueError('wrong refresh/registration scope')
    for k, value in launch.items():
        if k not in ['commands', 'recursive_kernel_check', 'canonical_source_guard'] and r[k] != value:
            raise ValueError('launch/terminal identity differs')
    results = ['C.' + row['name'] + '.' + n for row in g.OLD_ASSEMBLY['modules'] for n in row['results']]
    definitions = ['C.' + row['name'] + '.' + n for row in g.OLD_ASSEMBLY['modules'] for n in row['definitions']]
    if r['results'] != results or r['definitions'] != definitions or (len(results), len(definitions)) != (116, 32):
        raise ValueError('wrong complete declaration inventory')
    for table, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[table]) != set(g.MODULES):
            raise ValueError('incomplete fresh source/object inventory')
        for m, h in r[table].items():
            p = work / 'Coq' / (m.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != h:
                raise ValueError('fresh source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.MODULES}
    for kind in ['assumptions', 'contracts']:
        commands['lambda-refresh-' + kind] = ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('lambda_refresh_' + kind + '.v'))]
    commands.update(source=[sys.executable, '-B', str(g.OLD / 'check-lambda-public.py'), '--repo', str(g.REPO), '--coq', str(work / 'Coq')],
        **{'source-negative': [sys.executable, '-B', str(g.OLD / 'test-lambda-public.py'), str(g.REPO), str(work / 'Coq')]},
        kernel=g.KERNEL_COMMAND)
    if set(r['commands']) != set(commands) or set(launch['commands']) != set(commands) - {'source', 'source-negative', 'kernel'}:
        raise ValueError('wrong command inventory')
    for n, command in commands.items():
        row, log = r['commands'][n], work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or n in launch['commands'] and launch['commands'][n] != row):
            raise ValueError('command/exit/log evidence differs')
    report = (work / 'lambda-refresh-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^LAMBDA_REFRESH_(TYPE|DEF) (\S+)$', report) != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete/unquantified full report')
    deps = s.reports.assumptions((work / 'lambda-refresh-assumptions.log').read_text())
    if (deps != g.expected_dependencies() or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()} or
        r['closed_results'] != [n for n in results if not deps[n]] or len(r['closed_results']) != 60 or
        any(not ds <= g.EIGHT for ds in deps.values())):
        raise ValueError('dependency sets differ from checked counterparts')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    # Re-run the selected source guard, not just a receipt's true flag.
    source = g.load('lambda_refresh_source_recheck', g.OLD / 'check-lambda-public.py').check(g.REPO, work / 'Coq')
    if source != json.loads((work / 'source.log').read_text()):
        raise ValueError('selected source review differs')
    return dict(candidate=str(work), baseline_coverage='418/533', fresh_modules=28,
        added_sources=26, byte_identical_reused_sources=2, results=116, definitions=32, closed_results=60,
        initialized_global_entry_and_preservation_explicit=True, actual_init_fresh_call_witness=True,
        public_endpoint_inherited_assumptions=8, new_axioms=0, recursive_kernel_check=True,
        selected_canonical_source_guard=True, inherited_source_changes=0,
        c_evaluator_setup_proved=False, normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('review already recorded')
    result = review(work)
    commands = {'evidence-tests': s.run(work, [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'evidence-tests', 600)}
    if review(work) != result:
        raise ValueError('refreshed evidence changed during tests')
    r = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        assembly_sha256=s.sha((HERE / 'ASSEMBLY.json').read_bytes()), launch_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work), commands=commands,
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['check.py', 'review.py', 'test-review.py']},
        inherited_tools_sha256={str(p.relative_to(s.REPO)): s.sha(p.read_bytes()) for p in
            [g.OLD / 'review-normal.py', g.OLD / 'check-lambda-public.py', g.OLD / 'test-lambda-public.py']},
        normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(r, indent=2) + '\n',
               HERE / 'evidence-tests.log': (work / 'evidence-tests.log').read_text()})
    print('Refreshed initialized-lambda proof/source/evidence independently reviewed; no coverage added', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
