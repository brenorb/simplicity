"""Independent checked-proof/evidence review plus selected canonical guards."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_proof_review', HERE / 'check.py')
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
        r['modules'] != [g.MODULE] or r['fresh_modules'] != g.ROOTS or r['new_sources'] != [g.NEW] or r['endpoints'] != g.ENDPOINTS or
        r['recursive_kernel_check'] is not True or launch['recursive_kernel_check'] is not False or
        any(r[k] is not False for k in ['canonical_source_gate_complete', 'normal_registration', 'full_acceptance']) or
        r['coverage_added'] != 0):
        raise ValueError('wrong completed proof/canonical/admission scope')
    if any(launch[k] != r[k] for k in launch if k not in ['commands', 'recursive_kernel_check']):
        raise ValueError('pre-kernel and terminal identities differ')
    if (r['tools_sha256'] != {'check.py': s.sha((HERE / 'check.py').read_bytes())} or
        r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('tool/main/index/private identity drift')
    results, definitions = [], []
    for m in [g.MODULE]:
        p = work / 'Coq' / (m.replace('.', '/') + '.v')
        a, b = g.shared.declarations(p.read_text(), m)
        results += a
        definitions += b
        if p.is_symlink() or p.with_suffix('.vo').is_symlink():
            raise ValueError('shared mutable source/object')
        if (s.sha(p.read_bytes()) != r['source_sha256'][m] or
            s.sha(p.with_suffix('.vo').read_bytes()) != r['object_sha256'][m]):
            raise ValueError('fresh proof source/object hash differs')
    if (r['results'] != results or r['definitions'] != definitions or
        (len(results), len(definitions)) != (8, 5) or
        set(r['source_sha256']) != set(g.ROOTS) or set(r['object_sha256']) != set(g.ROOTS)):
        raise ValueError('wrong declaration/object inventory')
    for m in g.ROOTS:
        p = work / 'Coq' / (m.replace('.', '/') + '.v')
        if p.is_symlink() or p.with_suffix('.vo').is_symlink():
            raise ValueError('shared mutable execution source/object')
        if s.sha(p.read_bytes()) != r['source_sha256'][m] or s.sha(p.with_suffix('.vo').read_bytes()) != r['object_sha256'][m]:
            raise ValueError('fresh execution source/object differs: ' + m)
    report = (work / 'amount-literal-contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete/reordered full contracts')
    deps = s.reports.assumptions((work / 'amount-literal-assumptions.log').read_text())
    if (set(deps) != set(results) or r['dependencies'] != {n: sorted(ds) for n, ds in deps.items()} or
        any(not ds <= s.SIX for ds in deps.values()) or any(deps[n] != s.SIX for n in g.ENDPOINTS) or
        r['closed_results'] != [n for n in results if not deps[n]] or len(r['closed_results']) != 2):
        raise ValueError('actual dependency or closedness sets differ')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in g.ROOTS}
    commands.update({
        'amount-literal-assumptions': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'amount_literal_assumptions.v')],
        'amount-literal-contracts': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'amount_literal_contracts.v')],
        'ast': ['bash', 'C/check-elements-jets-generation.sh'],
        'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *[g.MODULE]]})
    if set(r['commands']) != set(commands) or set(launch['commands']) != set(commands) - {'ast', 'kernel'}:
        raise ValueError('wrong completed command inventory')
    for n, command in commands.items():
        row = r['commands'][n]
        log = work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
            (HERE / log.name).read_bytes() != log.read_bytes() or
            n in launch['commands'] and row != launch['commands'][n]):
            raise ValueError('command/flags/exit/log binding differs: ' + n)
    s.kernel.kernel((work / 'kernel.log').read_text(), sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    source = s.load('legacy_canonical_guard', HERE / 'check-source.py').check(work)
    if (source['canonical_pair_routing_reviewed'] is not True or source['whole_contracts_reviewed'] is not True or source['primitive_and_jet_codomain_distinguished'] is not True or source['explicit_word64_and_padding_reviewed'] is not True or
        source['caller_environment_construction_proved'] is not False or
        source['field_arithmetic_proved'] is not False or source['arbitrary_word_is_valid_field_element_claimed'] is not False or
        source['formal_host_library_equivalence'] is not False or source['normal_registration'] is not False):
        raise ValueError('source guard scope differs')
    return dict(candidate=str(work), new_results=8, new_definitions=5, closed_results=2,
        whole_c_endpoints=3, recursive_kernel_check=True, canonical_source_guard_reviewed=True,
        canonical_pair_routing_reviewed=True, explicit_word64_and_padding_reviewed=True, field_arithmetic_proved=False,
        inherited_source_changes=0, caller_environment_construction_proved=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)


def finish(work):
    if (HERE / 'EVIDENCE-REVIEW.json').exists():
        raise ValueError('review already recorded; inspect its existing receipt')
    result, commands = review(work), {}
    for stem, command in [
        ('source-review', [sys.executable, '-B', str(HERE / 'check-source.py'), str(work)]),
        ('source-negative', [sys.executable, '-B', str(HERE / 'test-source.py'), str(work)]),
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]:
        commands[stem] = s.run(work, command, stem, 600)
    review(work)
    r = dict(review=result, checked_sha256=s.sha((HERE / 'CHECKED.json').read_bytes()),
        launch_sha256=s.sha((HERE / 'RUN.json').read_bytes()), commands=commands,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
                      ['check.py', 'check-source.py', 'test-source.py', 'review.py', 'test-review.py']},
        canonical_source_gate_complete=True, normal_registration=False, full_acceptance=False)
    changes = {HERE / 'EVIDENCE-REVIEW.json': json.dumps(r, indent=2) + '\n'}
    for n in commands:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    s.changed(changes)
    print('Amount jet proof/source/evidence review complete; no normal registration or full acceptance', flush=True)


if __name__ == '__main__':
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'review':
        print(json.dumps(review(work), indent=2))
    elif sys.argv[1] == 'finish':
        finish(work)
    else:
        raise ValueError('usage: review.py review|finish PRIVATE_TREE')
