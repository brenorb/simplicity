"""Validate final-C-name timelock checks; preparation is not admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('timelock_final_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def source_paths(root):
    return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and
            (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} or
             p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}


def review():
    record = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base, objects = (Path(record[k]) for k in ['candidate', 'base_candidate', 'object_base_candidate'])
    coq = work / 'Coq'
    direct_path = HERE.parent / 'elements-direct-getters-admission/REVIEW.json'
    lock_path = HERE.parent / 'elements-lock/PREPARATION.json'
    direct, lock = json.loads(direct_path.read_text()), json.loads(lock_path.read_text())
    roots = ['C.jet_elements_is_final_local', 'C.jet_elements_lock_literal']
    order = ['C.jet_elements_tx_field_set', 'C.jet_elements_is_final_spec',
             'C.jet_elements_is_final_local', 'C.jet_elements_lock_spec',
             'C.jet_elements_lock_exec', 'C.jet_elements_lock_local', 'C.jet_elements_lock_literal']
    new_source = 'C/jet_elements_lock_literal.v'
    if (record['namespace'] != 'C' or record['roots'] != roots or record['missing_dependency_modules'] != order or
            record['new_sources'] != [new_source] or record['normal_registration'] is not False or
            record['coverage_added'] != 0 or record['full_acceptance'] is not False or
            str(base) != direct['review']['candidate'] or str(objects) != lock['candidate'] or
            record['base_review_sha256'] != support.sha(direct_path.read_bytes()) or
            record['object_base_preparation_sha256'] != support.sha(lock_path.read_bytes())):
        raise ValueError('wrong final-name timelock scope/source/object base')
    if (support.inputs.fingerprint(base / 'Coq', base) != direct['candidate_input_sha256'] or
            record['base_input_sha256'] != direct['candidate_input_sha256'] or
            support.inputs.fingerprint(objects / 'Coq', objects) != lock['candidate_input_sha256'] or
            support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
            support.index_hash() != record['staged_patch_sha256']):
        raise ValueError('source baseline/candidate/index drift')
    overlay = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
               'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv',
               'C/jet_assumptions.expected', 'C/jet_contracts.expected',
               'jet-coverage.py', 'test-jet-coverage.py', 'check-jets.sh', 'audit-jet-contracts.sh']
    overlay += [directory + '/' + name for directory in ['elements-tapleaf-literal', 'elements-hash-literal']
                for name in ['check-source.py', 'test-source.py']]
    if record['source_overlay'] != overlay:
        raise ValueError('unreviewed source-overlay inventory')
    inherited = source_paths(base / 'Coq')
    if source_paths(coq) != inherited | {new_source}:
        raise ValueError('non-additive final-name source inventory')
    for name in inherited:
        if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('inherited source/metadata/guard changed: ' + name)
    source = coq / new_source
    archive = HERE.parent / 'elements-lock/source/jet_elements_lock_literal.v.source'
    if source.read_bytes() != archive.read_bytes() or source.read_bytes() != (HERE / 'source/jet_elements_lock_literal.v.source').read_bytes():
        raise ValueError('final-name rebasing altered the literal proof')
    results, definitions = [], []
    for module in order:
        path = coq / (module.replace('.', '/') + '.v')
        code = support.safe_source(path.read_text(), module)
        results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
        obj = path.with_suffix('.vo')
        if (obj.is_symlink() or record['source_sha256'].get(module) != support.sha(path.read_bytes()) or
                record['object_sha256'].get(module) != support.sha(obj.read_bytes())):
            raise ValueError('fresh final-name source/object evidence differs')
    pure = ['C.jet_elements_lock_literal.' + n for n in ['elements_parse_lock_literal_matches', 'elements_lock_literal_program_matches']]
    if (record['results'] != results or record['definitions'] != definitions or record['pure_results'] != pure or
            set(record['source_sha256']) != set(order) or set(record['object_sha256']) != set(order)):
        raise ValueError('incomplete new results/definitions/closed bridges')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or {n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
            any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure)):
        raise ValueError('unreviewed assumptions/nonclosed bridge')
    original = {n.replace('LockLiteral.', 'C.', 1): ds for n, ds in lock['dependencies'].items()}
    if any(sorted(deps[n]) != original[n] for n in results):
        raise ValueError('namespace rebasing changed inherited dependency sets')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^TIMELOCK_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete final-name contract report')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    for package in ['elements-finality', 'elements-lock']:
        flags = [] if package == 'elements-finality' else ['--literal', new_source]
        positional = [] if package == 'elements-finality' else [new_source]
        commands[package + '-source'] = [sys.executable, '-B', str(HERE.parent / package / 'check-source.py'), '--repo', str(work), '--coq', '.', *flags]
        commands[package + '-negative'] = [sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.', *positional]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]
    if set(record['commands']) != set(commands):
        raise ValueError('missing final-name checker stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('wrong final-name command/exit/log evidence')
    tools = {'prepare.py': HERE / 'prepare.py'}
    tools.update({p + '/' + n: HERE.parent / p / n for p in ['elements-finality', 'elements-lock'] for n in ['check-source.py', 'test-source.py']})
    if record['tools_sha256'] != {n: support.sha(p.read_bytes()) for n, p in tools.items()}:
        raise ValueError('final-name source/replay tool drift')
    for name in ['assumptions.log', 'contracts.log', 'kernel.log', 'ast.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived final-name evidence changed')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate': str(work), 'namespace': 'C', 'jets_checked': 3, 'fresh_modules': len(order),
            'result_types': len(results), 'definitions': len(definitions), 'closed_bridges': len(pure),
            'inherited_sources_byte_identical': len(inherited), 'normal_registration': False,
            'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
