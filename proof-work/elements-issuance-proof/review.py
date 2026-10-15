"""Review the formal checkpoint and selected source ports; never register jets."""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('issuance_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    r = json.loads((HERE / 'CHECKED.json').read_text())
    work, base = Path(r['candidate']), Path(r['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-script-hash/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    lm, source = 'C.jet_elements_issuance_proof_literal', 'C/jet_elements_issuance_proof_literal.v'
    roots = ['C.jet_elements_input_hash_jets', 'C.jet_elements_current_input_jets', lm]
    originals = ['C.jet_elements_input_hash_jets.elements_issuance_' + p + '_proof_local_spec' for p in ['asset', 'token']]
    originals += ['C.jet_elements_current_input_jets.elements_current_issuance_' + p + '_proof_local_spec' for p in ['asset', 'token']]
    finals = [lm + '.elements_' + prefix + 'issuance_' + p + '_proof_literal_local_spec' for prefix in ['', 'current_'] for p in ['asset', 'token']]
    pure = [lm + '.elements_issuance_' + p + '_proof_view_matches' for p in ['asset', 'token']]
    if (str(base) != prior['candidate'] or r['base_input_sha256'] != prior['candidate_input_sha256'] or
            r['prior_preparation_sha256'] != support.sha(prior_path.read_bytes()) or r['new_source'] != source or
            r['fresh_modules'] != [lm] or r['reused_checked_modules'] != prior['fresh_modules'] or r['roots'] != roots or
            r['endpoints'] != finals or r['original_endpoints'] != originals or r['closed_view_lemmas'] != pure or
            r['source_fidelity_review_complete'] is not False or r['normal_registration'] is not False or
            r['coverage_added'] != 0 or r['full_acceptance'] is not False):
        raise ValueError('wrong formal checkpoint/base scope')
    if (support.inputs.fingerprint(base / 'Coq', base) != r['base_input_sha256'] or
            support.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or support.index_hash() != r['staged_patch_sha256']):
        raise ValueError('base/candidate/index drift')
    paths = support.load('issuance_review_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    inherited = paths(base / 'Coq')
    if paths(coq) != inherited | {source}:
        raise ValueError('non-additive source inventory')
    for n in inherited:
        if (coq / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source/metadata drift: ' + n)
    for m in prior['fresh_modules']:
        for suffix, key in [('.v', 'source_sha256'), ('.vo', 'object_sha256')]:
            p = coq / (m.replace('.', '/') + suffix)
            if p.is_symlink() or support.sha(p.read_bytes()) != prior[key][m]:
                raise ValueError('reused checked dependency drift')
    p = coq / source
    if (p.read_bytes() != (HERE / 'source/jet_elements_issuance_proof_literal.v.source').read_bytes() or
            r['source_sha256'] != support.sha(p.read_bytes()) or p.with_suffix('.vo').is_symlink() or
            r['object_sha256'] != support.sha(p.with_suffix('.vo').read_bytes())):
        raise ValueError('fresh proof source/object/archive drift')
    code = support.safe_source(p.read_text(), lm)
    results = [lm + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
    definitions = [lm + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
    if (len(results), len(definitions)) != (10, 6) or r['results'] != results or r['definitions'] != definitions:
        raise ValueError('incomplete new declaration inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results + originals) or any(not ds <= support.SIX for ds in deps.values()) or
            {n: sorted(ds) for n, ds in deps.items()} != r['dependencies'] or any(deps[n] for n in pure) or
            any(deps[a] != deps[b] for a, b in zip(finals, originals)) or
            any(sorted(deps[n]) != prior['dependencies'][n] for n in originals)):
        raise ValueError('unreviewed assumptions or nonclosed view lemmas')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or re.findall(r'(?m)^ISSUANCE_PROOF_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full contracts')
    commands = {'literal': ['bash', 'build-jets.sh', '--coqc', '-q', source],
                **{n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']},
                'ast': ['bash', 'C/check-elements-jets-generation.sh'],
                'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]}
    if set(commands) != set(r['commands']) or r['tools_sha256'] != {'check.py': support.sha((HERE / 'check.py').read_bytes())}:
        raise ValueError('wrong compiler/checker/tool inventory')
    for n, command in commands.items():
        row = r['commands'][n]
        log = work / (n + '.log')
        if (row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != support.sha(log.read_bytes()) or
                log.read_bytes() != (HERE / (n + '.log')).read_bytes()):
            raise ValueError('wrong command/flags/exit/archive evidence')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    guard = support.load('issuance_review_source', HERE / 'check-source.py')
    guard.check(work, coq, p)
    return {'candidate': str(work), 'jets_checked': 4, 'new_results': 10, 'new_definitions': 6,
            'closed_view_lemmas': 2, 'inherited_sources_byte_identical': len(inherited),
            'fresh_modules': 1, 'reused_checked_modules': 18, 'selected_canonical_correspondence_reviewed': True,
            'formal_host_lens_equivalence': False, 'formal_host_crypto_equivalence': False,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


def finish():
    result = review()
    work = Path(result['candidate'])
    commands = {
        'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', str(work / 'Coq'),
                   '--literal', str(work / 'Coq/C/jet_elements_issuance_proof_literal.v')],
        'source-negative': [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), str(work / 'Coq'),
                            str(work / 'Coq/C/jet_elements_issuance_proof_literal.v')],
        'evidence-negative': [sys.executable, '-B', str(HERE / 'test-review.py')],
    }
    checked = {n: support.run(work, c, n, 1800) for n, c in commands.items()}
    review()
    record = {'review': result, 'checked_receipt_sha256': support.sha((HERE / 'CHECKED.json').read_bytes()),
              'checks': checked, 'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in
               ['check-source.py', 'test-source.py', 'review.py', 'test-review.py']}, 'full_acceptance': False}
    changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
    for n in checked:
        changes[HERE / (n + '.log')] = (work / (n + '.log')).read_text()
    support.changed(changes)
    print('Four issuance-proof selected source ports and formal evidence reviewed; normal admission still required', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--finish', action='store_true')
    args = p.parse_args()
    finish() if args.finish else print(json.dumps(review(), indent=2))
