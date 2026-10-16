"""Read-only checker/evidence review; no token jet equivalence claim."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('token_zero_check_evidence', HERE / 'check-zero-init.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s


def review(work):
    base = g.tree(work)
    r = json.loads((HERE / 'ZERO-INIT-CHECKED.json').read_text())
    start = json.loads((HERE / 'ZERO-INIT-RUN.json').read_text())
    if (r['candidate'] != str(work) or r['module'] != g.MODULE or
        r['base_receipt_sha256'] != s.sha(g.BASE_RECEIPT.read_bytes()) or
        r['base_input_sha256'] != base['candidate_input_sha256'] or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
        r['checker_sha256'] != s.sha((HERE / 'check-zero-init.py').read_bytes()) or
        r['recursive_kernel_check'] is not True or start['recursive_kernel_check'] is not False or
        r['whole_jet_equivalence'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False):
        raise ValueError('helper source/checker/main/index/scope differs')
    if any(start[n] != r[n] for n in start if n not in ['commands', 'recursive_kernel_check']):
        raise ValueError('launch/terminal helper identity differs')
    source = work / 'Coq' / g.NEW
    if (source.is_symlink() or source.with_suffix('.vo').is_symlink() or
        r['source_sha256'] != s.sha(source.read_bytes()) or
        r['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes())):
        raise ValueError('fresh helper source/object differs')
    results, definitions = g.shared.declarations(source.read_text(), g.MODULE)
    if results != r['results'] or definitions != r['definitions'] or (len(results), len(definitions)) != (5, 4):
        raise ValueError('helper declaration inventory differs')
    report = (work / 'token-zero-init-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('missing/truncated full helper reports')
    deps = s.reports.assumptions((work / 'token-zero-init-assumptions.log').read_text())
    if (set(deps) != set(results) or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()} or
        any(not ds <= s.SIX for ds in deps.values()) or
        deps[g.MODULE + '.token_zero_init_shape'] or deps[g.MODULE + '.exec_token_zero_init'] != s.SIX):
        raise ValueError('helper dependency sets differ')
    commands = {
        'fresh': ['bash', 'build-jets.sh', '--coqc', '-q', g.NEW],
        'token-zero-init-assumptions': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'token_zero_init_assumptions.v')],
        'token-zero-init-contracts': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'token_zero_init_contracts.v')],
        'ast': ['bash', 'C/check-elements-jets-generation.sh'],
        'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', g.MODULE]}
    if set(r['commands']) != set(commands) or set(start['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('wrong completed helper command inventory')
    for n, command in commands.items():
        row = r['commands'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / (n + '.log')).read_bytes()) or
            (work / (n + '.log')).read_bytes() != (HERE / (n + '.log')).read_bytes() or
            n in start['commands'] and row != start['commands'][n]):
            raise ValueError('helper command/flags/exit/log differs: ' + n)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    return dict(candidate=str(work), actual_compound_shape_checked=True, results=5, definitions=4,
        recursive_kernel_check=True, unchanged_inherited_sources=True,
        whole_jet_equivalence=False, coverage_added=0, full_acceptance=False)


if __name__ == '__main__':
    work = Path(sys.argv[1]).resolve()
    result = review(work)
    if sys.argv[2:] == ['--record']:
        if (HERE / 'ZERO-INIT-REVIEW.json').exists():
            raise ValueError('helper review already recorded')
        r = dict(review=result, checked_sha256=s.sha((HERE / 'ZERO-INIT-CHECKED.json').read_bytes()),
            launch_sha256=s.sha((HERE / 'ZERO-INIT-RUN.json').read_bytes()),
            reviewer_sha256=s.sha(Path(__file__).read_bytes()),
            candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
            whole_jet_equivalence=False, coverage_added=0, full_acceptance=False)
        s.changed({HERE / 'ZERO-INIT-REVIEW.json': json.dumps(r, indent=2) + '\n'})
    elif sys.argv[2:]:
        raise ValueError('usage: review-zero-init.py PRIVATE_TREE [--record]')
    print(json.dumps(result, indent=2))
