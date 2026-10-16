"""Second read plus opcode-index execution evidence; no whole-jet or canonical admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('txid_checked', HERE / 'check.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review(work):
    prior, base = g.tree(work)
    r = json.loads((HERE / 'CHECKED.json').read_text())
    launch = json.loads((HERE / 'RUN.json').read_text())
    if (r['candidate'] != str(work) or r['base_candidate'] != str(base) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['base_receipt_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        r['base_input_sha256'] != prior['candidate_input_sha256'] or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
        r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())}):
        raise ValueError('source/tool/index/checkpoint differs')
    if (r['modules'] != g.MODULES or r['fresh_modules'] != g.ROOTS or
        r['new_sources'] != g.NEW_SOURCES or r['endpoints'] != g.ENDPOINTS or
        r['recursive_kernel_check'] is not True or launch['recursive_kernel_check'] is not False or
        any(r[n] is not False for n in ['canonical_source_gate_complete', 'normal_registration', 'full_acceptance']) or
        r['coverage_added'] != 0 or r['whole_c_endpoints'] != 0 or r['execution_helpers'] != g.EXECUTION_RESULTS):
        raise ValueError('wrong proof/admission scope')
    for k in launch:
        if k not in ['commands', 'recursive_kernel_check'] and launch[k] != r[k]:
            raise ValueError('launch/terminal identity differs')
    results, definitions = [], []
    for m, n in zip(g.MODULES, g.NEW_SOURCES):
        a, b = g.shared.declarations((work / 'Coq' / n).read_text(), m)
        results += a
        definitions += b
    if (r['results'] != results or r['definitions'] != definitions or
        (len(results), len(definitions)) != (8, 4)):
        raise ValueError('wrong declaration inventory')
    for field, suffix in [('source_sha256', '.v'), ('object_sha256', '.vo')]:
        if set(r[field]) != set(g.ROOTS):
            raise ValueError('incomplete fresh source/object inventory')
        for m in g.ROOTS:
            p = work / 'Coq' / (m.replace('.', '/') + suffix)
            if p.is_symlink() or s.sha(p.read_bytes()) != r[field][m]:
                raise ValueError('fresh source/object differs')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.ROOTS}
    for n in ['assumptions', 'contracts']:
        commands['read-index-' + n] = ['bash', 'build-jets.sh', '--coqc', '-q', str(work / ('read_index_' + n + '.v'))]
    commands.update(ast=['bash', 'C/check-elements-jets-generation.sh'],
        kernel=['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *g.MODULES])
    if set(r['commands']) != set(commands) or set(launch['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('wrong command inventory')
    for n, command in commands.items():
        row = r['commands'][n]
        log = work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            n in launch['commands'] and launch['commands'][n] != row):
            raise ValueError('terminal command/log differs')
    report = (work / 'read-index-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full reports')
    deps = s.reports.assumptions((work / 'read-index-assumptions.log').read_text())
    four = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    evaluations = {g.MODULES[0] + '.' + n for n in [
        'write_effect_private_interleaved', 'elements_null_data_count_path_read_preserved',
        'elements_null_data_path_read_preserved', 'elements_null_data_selected_read_preserved',
        'elements_null_data_selected_private_fresh', 'elements_null_data_count_blocks_fresh']}
    expected = {n: s.SIX if n in g.EXECUTION_RESULTS else four if n in evaluations else set() for n in results}
    if (deps != expected or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()} or
        r['closed_results'] != [n for n in results if not deps[n]] or len(r['closed_results']) != 1):
        raise ValueError('dependency or closedness claim differs')
    s.kernel.kernel((work / 'kernel.log').read_text(),
                    sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    return dict(candidate=str(work), results=8, definitions=4, actual_second_read_composed=True,
        whole_c_endpoints=0, recursive_kernel_check=True, inherited_source_changes=0,
        canonical_source_gate_complete=False, normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('review already recorded; inspect its existing receipt')
    result, commands = review(work), {}
    for stem, command in [
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]:
        commands[stem] = s.run(work, command, stem, 600)
    if review(work) != result:
        raise ValueError('review changed during source/evidence checks')
    r = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        launch_sha256=s.sha((HERE / 'RUN.json').read_bytes()), commands=commands,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
                      ['check.py', 'review.py', 'test-review.py']},
        canonical_source_gate_complete=False, normal_registration=False, full_acceptance=False)
    s.changed({HERE / 'EVIDENCE-REVIEW.json': json.dumps(r, indent=2) + '\n',
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in commands}})
    print('Read/index composition proof/evidence review complete; no whole-jet or normal admission claim', flush=True)


if __name__ == '__main__':
    if len(sys.argv) == 2:
        print(json.dumps(review(Path(sys.argv[1]).resolve()), indent=2))
    elif len(sys.argv) == 3 and sys.argv[1] == 'finish':
        finish(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: review.py [finish] PRIVATE_TREE')
