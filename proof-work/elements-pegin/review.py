"""Review two pegin C-to-literal contracts and all retained verification evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('pegin_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(r['candidate']), Path(r['base_candidate'])
    coq, literal = work / 'Coq', work / 'Proof/jet_elements_pegin_literal.v'
    prior_path = HERE.parent / 'elements-check-lock-normal/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    order = ['C.jet_elements_' + n for n in [
        'indexed_ptr_then', 'indexed_ptr', 'hash_helpers', 'indexed_ptr_jets', 'hash_elem', 'pegin_local',
        'input_hash_jets', 'asset_helper', 'asset_jets', 'amt_helper', 'indexed_gen', 'indexed_ptr2',
        'amount_jets', 'issuance_helper', 'issuance_jets', 'issuance_amount_jets', 'current_ptr',
        'current_ptr_jets', 'current_gen', 'current_input_jets', 'current_gen_jets']]
    lm = 'PeginLiteral.jet_elements_pegin_literal'
    roots = ['C.jet_elements_pegin_local', 'C.jet_elements_current_gen_jets', lm]
    originals = ['C.jet_elements_pegin_local.elements_input_pegin_hash_local_spec',
                 'C.jet_elements_current_gen_jets.elements_current_pegin_local_spec']
    finals = [lm + '.elements_' + p + '_pegin_literal_local_spec' for p in ['input', 'current']]
    if (r['namespace'] != 'PeginLiteral' or r['fresh_modules'] != order or r['literal_module'] != lm or
            r['roots'] != roots or r['originals'] != originals or r['finals'] != finals or
            r['normal_registration'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False or
            str(base) != prior['candidate'] or r['candidate_input_sha256'] != prior['candidate_input_sha256'] or
            r['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong pegin scope/source base')
    if (support.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or
            support.inputs.fingerprint(base / 'Coq', base) != r['candidate_input_sha256'] or
            support.index_hash() != r['staged_patch_sha256']):
        raise ValueError('pegin source-copy/index identity changed')
    paths = {m: coq / (m.replace('.', '/') + '.v') for m in order}
    paths[lm] = literal
    results, definitions = [], []
    for m, path in paths.items():
        if m != lm and path.read_bytes() != (base / 'Coq' / path.relative_to(coq)).read_bytes():
            raise ValueError('inherited source changed')
        archive = HERE / 'source' / (m.split('.')[-1] + '.v.source')
        obj = path.with_suffix('.vo')
        if (path.read_bytes() != archive.read_bytes() or obj.is_symlink() or
                r['source_sha256'].get(m) != support.sha(path.read_bytes()) or
                r['object_sha256'].get(m) != support.sha(obj.read_bytes())):
            raise ValueError('pegin source/archive/object mismatch')
        code = support.safe_source(path.read_text(), m)
        results += [m + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += [m + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (r['results'] != results or r['definitions'] != definitions or
            set(r['source_sha256']) != set(paths) or set(r['object_sha256']) != set(paths)):
        raise ValueError('incomplete pegin public/source/object inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
            {n: sorted(ds) for n, ds in deps.items()} != r['dependencies'] or
            any(deps[a] != deps[b] for a, b in zip(finals, originals))):
        raise ValueError('new/unreviewed pegin assumptions')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^PEGIN_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete pegin deep records')
    flags = ['-Q', str(work / 'Proof'), 'PeginLiteral']
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands['literal'] = ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(literal)]
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    commands['source'] = [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.', '--literal', str(literal)]
    commands['source-negative'] = [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal)]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', *roots]
    if set(commands) != set(r['commands']):
        raise ValueError('missing pegin compiler/checker stage')
    for n, command in commands.items():
        row = r['commands'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (n + '.log')).read_bytes())):
            raise ValueError('wrong pegin compiler/checker command/exit/log')
    if r['tools_sha256'] != {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']}:
        raise ValueError('checked pegin tool drift')
    for n in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
        if (HERE / n).read_bytes() != (work / n).read_bytes():
            raise ValueError('archived pegin evidence changed')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('pegin_review_source', HERE / 'check-source.py')
    source_gate.check(work, coq, literal)
    return {'candidate': str(work), 'jets_checked': ['input_pegin', 'current_pegin'], 'fresh_C_modules': len(order),
            'new_literal_modules': 1, 'result_types': len(results), 'definitions': len(definitions),
            'all_three_indexed_presence_cases_retained': True, 'recursive_kernel_and_exact_AST': True,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
