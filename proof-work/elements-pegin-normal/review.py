"""Review final-C-name pegin preparation; no registration/acceptance claim."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('pegin_normal_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def source_paths(root):
    return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and
            (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} or
             p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}


def review():
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(r['candidate']), Path(r['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-pegin/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    new_source, lm = 'C/jet_elements_pegin_literal.v', 'C.jet_elements_pegin_literal'
    order = prior['fresh_modules'] + [lm]
    roots = ['C.jet_elements_pegin_local', 'C.jet_elements_current_gen_jets', lm]
    if (len(order) != 22 or len(set(order)) != 22 or r['namespace'] != 'C' or r['roots'] != roots or
            r['new_sources'] != [new_source] or r['missing_dependency_modules'] != order or
            r['normal_registration'] is not False or r['coverage_added'] != 0 or r['full_acceptance'] is not False or
            str(base) != prior['candidate'] or r['base_input_sha256'] != prior['candidate_input_sha256'] or
            r['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong final-name pegin scope/dependency base')
    if (support.inputs.fingerprint(base / 'Coq', base) != r['base_input_sha256'] or
            support.inputs.fingerprint(coq, work) != r['candidate_input_sha256'] or
            support.index_hash() != r['staged_patch_sha256']):
        raise ValueError('base/candidate/index changed')
    inherited = source_paths(base / 'Coq')
    if source_paths(coq) != inherited | {new_source}:
        raise ValueError('non-additive final-name source inventory')
    for n in inherited:
        if (coq / n).read_bytes() != (base / 'Coq' / n).read_bytes():
            raise ValueError('inherited source/metadata/registry drift: ' + n)
    source = coq / new_source
    if (source.read_bytes() != (HERE.parent / 'elements-pegin/source/jet_elements_pegin_literal.v.source').read_bytes() or
            source.read_bytes() != (HERE / 'source/jet_elements_pegin_literal.v.source').read_bytes()):
        raise ValueError('namespace rebasing changed the literal proof')
    results, definitions = [], []
    for m in order:
        path = coq / (m.replace('.', '/') + '.v')
        code = support.safe_source(path.read_text(), m)
        results += [m + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
        definitions += [m + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
        obj = path.with_suffix('.vo')
        if (obj.is_symlink() or r['source_sha256'].get(m) != support.sha(path.read_bytes()) or
                r['object_sha256'].get(m) != support.sha(obj.read_bytes())):
            raise ValueError('final-name source/object evidence differs')
    if (r['results'] != results or r['definitions'] != definitions or
            set(r['source_sha256']) != set(order) or set(r['object_sha256']) != set(order)):
        raise ValueError('incomplete apostrophe-aware result/source inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    old_deps = {n.replace('PeginLiteral.', 'C.', 1): ds for n, ds in prior['dependencies'].items()}
    if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
            any(sorted(ds) != old_deps[n] for n, ds in deps.items()) or
            {n: sorted(ds) for n, ds in deps.items()} != r['dependencies']):
        raise ValueError('final-name assumptions differ from checked source')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^NORMAL_PEGIN_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete final-name type/definition report')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    commands['source'] = [sys.executable, '-B', str(HERE.parent / 'elements-pegin/check-source.py'), '--repo', str(work), '--coq', '.', '--literal', new_source]
    commands['source-negative'] = [sys.executable, '-B', str(HERE.parent / 'elements-pegin/test-source.py'), str(work), '.', new_source]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]
    if set(commands) != set(r['commands']):
        raise ValueError('missing final-name pegin compiler/checker stage')
    for n, command in commands.items():
        row = r['commands'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (n + '.log')).read_bytes())):
            raise ValueError('wrong final-name command/exit/log evidence')
    tools = {'prepare.py': support.sha((HERE / 'prepare.py').read_bytes()),
             **{n: support.sha((HERE.parent / 'elements-pegin' / n).read_bytes()) for n in ['check-source.py', 'test-source.py']}}
    if r['tools_sha256'] != tools:
        raise ValueError('final-name checked tool drift')
    for n in ['assumptions.log', 'contracts.log', 'ast.log', 'kernel.log']:
        if (HERE / n).read_bytes() != (work / n).read_bytes():
            raise ValueError('archived final-name evidence differs')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('normal_pegin_review_source', HERE.parent / 'elements-pegin/check-source.py')
    source_gate.check(work, coq, source)
    return {'candidate': str(work), 'namespace': 'C', 'jets_checked': 2, 'fresh_modules': len(order),
            'result_types': len(results), 'definitions': len(definitions), 'inherited_sources_byte_identical': len(inherited),
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
