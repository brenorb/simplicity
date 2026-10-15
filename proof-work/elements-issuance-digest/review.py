"""Review six final-name issuance-digest C contracts without admitting coverage."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('annex_hash_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(r['candidate']), Path(r['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-annex-hash/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    lm, new_source = 'C.jet_elements_issuance_digest_literal', 'C/jet_elements_issuance_digest_literal.v'
    roots = ['C.jet_elements_issuance_jets', 'C.jet_elements_current_input_jets', lm]
    if (r['namespace'] != 'C' or r['roots'] != roots or r['new_sources'] != [new_source] or
            r['normal_registration'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False or
            str(base) != prior['candidate'] or r['base_input_sha256'] != prior['candidate_input_sha256'] or
            r['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong issuance-digest proof/base scope')
    if (support.inputs.fingerprint(base / 'Coq', base) != r['base_input_sha256'] or
            support.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or support.index_hash() != r['staged_patch_sha256']):
        raise ValueError('checked base/candidate/index drift')
    source_paths = support.load('annex_hash_review_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
    inherited = source_paths(base / 'Coq')
    if source_paths(coq) != inherited | {new_source}:
        raise ValueError('non-additive issuance-digest source inventory')
    for n in inherited:
        if (coq / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source/metadata/registry drift: ' + n)
    if (coq / new_source).read_bytes() != (HERE / 'source/jet_elements_issuance_digest_literal.v.source').read_bytes():
        raise ValueError('archived/checked proof differ')
    seen, visiting, order = set(), set(), []
    manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
    def visit(m):
        if m in seen:
            return
        if m in visiting:
            raise ValueError('cyclic issuance-digest dependency')
        visiting.add(m)
        code = support.safe_source((coq / (m.replace('.', '/') + '.v')).read_text(), m)
        for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
            for d in block.split():
                if d.startswith('C.'):
                    visit(d)
        visiting.remove(m)
        seen.add(m)
        if m.replace('.', '/') + '.v' not in manifest:
            order.append(m)
    visit(lm)
    if len(order) != 25 or r['fresh_modules'] != order:
        raise ValueError('wrong fresh dependency closure')
    results, definitions = [], []
    for m in order:
        path = coq / (m.replace('.', '/') + '.v')
        code = support.safe_source(path.read_text(), m)
        results += [m + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += [m + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
        obj = path.with_suffix('.vo')
        if obj.is_symlink() or r['source_sha256'].get(m) != support.sha(path.read_bytes()) or r['object_sha256'].get(m) != support.sha(obj.read_bytes()):
            raise ValueError('fresh source/object evidence differs')
    if (r['results'] != results or r['definitions'] != definitions or
            set(r['source_sha256']) != set(order) or set(r['object_sha256']) != set(order) or
            sum(n.startswith(lm + '.') for n in results) != 13 or sum(n.startswith(lm + '.') for n in definitions) != 6):
        raise ValueError('incomplete apostrophe-aware result/definition inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
            {n: sorted(ds) for n, ds in deps.items()} != r['dependencies'] or
            any(deps[n] for n in r['closed_shared_lemmas'])):
        raise ValueError('new/unreviewed assumptions or nonclosed generic conversion')
    for n, ds in deps.items():
        if not n.startswith(lm + '.') and sorted(ds) != prior['dependencies'][n]:
            raise ValueError('inherited dependency set changed')
    families = ['reissuance_blinding', 'new_issuance_contract', 'reissuance_entropy']
    originals = [('C.jet_elements_current_input_jets.' if current else 'C.jet_elements_issuance_jets.') +
                 'elements_' + ('current_' if current else '') + n + '_local_spec'
                 for n in families for current in [False, True]]
    endpoints = [lm + '.elements_' + ('current_' if current else '') + n + '_literal_local_spec'
                 for n in families for current in [False, True]]
    pure = [lm + '.elements_issuance_optional_digest_literal_matches']
    if (r['endpoints'] != endpoints or r['closed_shared_lemmas'] != pure or
            any(deps[n] for n in pure) or any(deps[a] != deps[b] for a, b in zip(endpoints, originals))):
        raise ValueError('wrong endpoint assumptions or nonclosed shared lemmas')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or re.findall(r'(?m)^ISSUANCE_DIGEST_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete type/definition report')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    commands['source'] = [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', str(coq), '--literal', str(coq / new_source)]
    commands['source-negative'] = [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), str(coq), str(coq / new_source)]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]
    if set(commands) != set(r['commands']):
        raise ValueError('missing checker/compiler stage')
    for n, command in commands.items():
        row = r['commands'][n]
        if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != support.sha((work / (n + '.log')).read_bytes()):
            raise ValueError('wrong command/flags/exit/log')
    if r['tools_sha256'] != {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']}:
        raise ValueError('checked tool drift')
    for n in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
        if (HERE / n).read_bytes() != (work / n).read_bytes():
            raise ValueError('archived check evidence differs')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('annex_hash_review_source', HERE / 'check-source.py')
    source_gate.check(work, coq, coq / new_source)
    return {'candidate': str(work), 'namespace': 'C', 'jets_checked': 6, 'fresh_modules': len(order),
            'result_types': len(results), 'definitions': len(definitions), 'new_results': 13, 'new_definitions': 6,
            'inherited_sources_byte_identical': len(inherited), 'closed_shared_lemmas': 1,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
