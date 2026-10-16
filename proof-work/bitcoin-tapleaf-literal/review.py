"""Independent literal TapLeaf source/object/command/type/kernel review.

Bind the immutable accepted418 history, not an obsolete exact-current-main
check: a later source-only successor may reuse this checked proof unchanged.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('tapleaf_checked', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    launch = json.loads((HERE / 'RUN.json').read_text())
    if (r['modules'] != [g.MODULE] or r['fresh_modules'] != g.ROOTS or
        r['new_sources'] != [g.NEW] or r['endpoints'] != [g.ENDPOINT] or
        r['closed_results'] != g.PURE or r['recursive_kernel_check'] is not True or
        launch['recursive_kernel_check'] is not False or r['coverage_added'] != 0 or
        any(r[n] is not False for n in ['canonical_source_gate_complete',
            'c_environment_builder_establishment', 'normal_registration', 'full_acceptance'])):
        raise ValueError('wrong tapleaf proof/admission scope')
    for n, value in launch.items():
        if n not in ['commands', 'recursive_kernel_check'] and r[n] != value:
            raise ValueError('tapleaf launch/terminal identity differs')
    if (r['candidate'] != str(work) or r['staged_patch_sha256'] != s.index_hash() or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('tapleaf candidate/index/checker identity differs')
    results, definitions = g.shared.declarations((work / 'Coq' / g.NEW).read_text(), g.MODULE)
    if (r['results'] != results or r['definitions'] != definitions or
        (len(results), len(definitions)) != (4, 6) or set(results) != set(g.PURE + [g.ENDPOINT])):
        raise ValueError('wrong complete tapleaf declaration inventory')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.ROOTS):
            raise ValueError('incomplete tapleaf fresh source/object inventory')
        for m, h in r[field].items():
            p = work / 'Coq' / (m.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != h:
                raise ValueError('fresh tapleaf source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.ROOTS}
    for n in ['assumptions', 'contracts']:
        commands['bitcoin-tapleaf-literal-' + n] = ['bash', 'build-jets.sh', '--coqc', '-q',
            str(work / ('bitcoin_tapleaf_literal_' + n + '.v'))]
    commands.update(ast=['bash', 'C/check-bitcoin-jets-generation.sh'], kernel=g.KERNEL)
    if set(r['commands']) != set(commands) or set(launch['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('incomplete tapleaf command inventory')
    for n, command in commands.items():
        row, log = r['commands'][n], work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            n in launch['commands'] and launch['commands'][n] != row):
            raise ValueError('tapleaf terminal command/exit/log differs')
    report = (work / 'bitcoin-tapleaf-literal-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full tapleaf type/definition reports')
    deps = s.reports.assumptions((work / 'bitcoin-tapleaf-literal-assumptions.log').read_text())
    expected = {n: set() for n in g.PURE}
    expected[g.ENDPOINT] = s.SIX
    if deps != expected or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()}:
        raise ValueError('tapleaf closedness/assumptions differ')
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source = s.load('tapleaf_literal_source', HERE / 'check-source.py').check(work)
    if (source['canonical_tapleaf_source_review_complete'] is not True or
        source['whole_contracts_reviewed'] is not True or source['selected_sha_helpers_reviewed'] is not True or
        source['caller_environment_construction_proved'] is not False or
        source['formal_host_library_equivalence'] is not False or source['normal_registration'] is not False):
        raise ValueError('tapleaf canonical/caller source-review scope differs')
    base, actual = g.tree(work)
    historical = s.load('tapleaf_historical_input_map', g.BASE / 'prepare-integration.py').input_map(base)
    if (r['base_candidate'] != str(base) or r['main_inputs'] != historical or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['base_input_sha256'] != actual['audit_input_sha256'] or
        r['base_main_acceptance_sha256'] != s.sha((g.BASE / 'MAIN-ACCEPTANCE.json').read_bytes()) or
        r['base_installation_sha256'] != s.sha((g.BASE / 'INSTALLATION.json').read_bytes())):
        raise ValueError('tapleaf immutable source/base checkpoint differs')
    return dict(candidate=str(work), results=4, definitions=6, closed_results=3, whole_c_endpoints=1,
        recursive_kernel_check=True, inherited_source_changes=0,
        canonical_tapleaf_source_review_complete=True, selected_sha_helpers_reviewed=True,
        caller_environment_construction_proved=False, formal_host_library_equivalence=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('tapleaf review already recorded; inspect existing receipt')
    before, index = s.input_map(), s.index_hash()
    result, commands = review(work), {}
    for stem, command in [
        ('source-review', [sys.executable, '-B', str(HERE / 'check-source.py'), str(work)]),
        ('source-negative', [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)]),
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]:
        commands[stem] = s.run(work, command, stem, 600)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('tapleaf evidence/source/main/index changed during review')
    record = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        launch_sha256=s.sha((HERE / 'RUN.json').read_bytes()), commands=commands,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
            ['check.py', 'check-source.py', 'source-model.json', 'test-source.py', 'review.py', 'test-review.py']},
        canonical_source_gate_complete=True, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(record, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Literal TapLeaf proof/source/evidence independently reviewed; normal registration remains', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
