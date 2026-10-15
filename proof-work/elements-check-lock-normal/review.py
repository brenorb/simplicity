"""Review final C namespace for all five timelock jets, without admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('final_check_lock_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def source_paths(root):
    return {str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and
            (p.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} or
             p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in')}


def review():
    record = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-check-lock/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    roots = ['C.jet_elements_is_final_local', 'C.jet_elements_lock_literal', 'C.jet_elements_check_lock_literal']
    new_sources = ['C/jet_application_partial_transport.v', 'C/jet_elements_check_lock_literal.v']
    order = ['C.jet_elements_tx_field_set', 'C.jet_elements_is_final_spec', 'C.jet_elements_is_final_local',
             'C.jet_elements_lock_spec', 'C.jet_elements_lock_exec', 'C.jet_elements_lock_local',
             'C.jet_elements_lock_literal', 'C.jet_elements_prim_sem', 'C.jet_elements_bool_wrapper',
             'C.jet_elements_check_lock', 'C.jet_application_partial_transport', 'C.jet_elements_check_lock_literal']
    references = ['C.jet_elements_sequence_literal.application_jet_local_spec_sep_pointwise']
    pure = ['C.jet_elements_lock_literal.elements_parse_lock_literal_matches',
            'C.jet_elements_lock_literal.elements_lock_literal_program_matches',
            'C.jet_elements_check_lock_literal.elements_check_lock_literal_program_matches']
    if (record['namespace'] != 'C' or record['roots'] != roots or record['new_sources'] != new_sources or
            record['missing_dependency_modules'] != order or record['pure_results'] != pure or
            record['reference_results'] != references or record['normal_registration'] is not False or
            record['coverage_added'] != 0 or record['full_acceptance'] is not False or
            str(base) != prior['candidate'] or record['base_input_sha256'] != prior['candidate_input_sha256'] or
            record['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong final-name check-lock source/dependency scope')
    if (support.inputs.fingerprint(base / 'Coq', base) != record['base_input_sha256'] or
            support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
            support.index_hash() != record['staged_patch_sha256']):
        raise ValueError('base/candidate/index identity changed')
    inherited = source_paths(base / 'Coq')
    if source_paths(coq) != inherited | set(new_sources):
        raise ValueError('non-additive final-name source inventory')
    for name in inherited:
        if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
            raise ValueError('inherited source/metadata/registry differs: ' + name)
    for name in new_sources:
        source = (HERE.parent / 'elements-check-lock/source' / (Path(name).name + '.source')).read_text()
        if name.endswith('jet_elements_check_lock_literal.v'):
            source = source.replace('Require Import CheckLockReview.jet_application_partial_transport.',
                                    'Require Import C.jet_application_partial_transport.')
        if ((coq / name).read_text() != source or
                (coq / name).read_bytes() != (HERE / 'source' / (Path(name).name + '.source')).read_bytes()):
            raise ValueError('namespace rebasing altered proof text')
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
    if (record['results'] != results or record['definitions'] != definitions or
            set(record['source_sha256']) != set(order) or set(record['object_sha256']) != set(order)):
        raise ValueError('incomplete final-name public/source/object inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    old_deps = {n.replace('CheckLockReview.', 'C.', 1): ds for n, ds in prior['dependencies'].items()}
    if (set(deps) != set(results + references) or any(not ds <= support.SIX for ds in deps.values()) or
            any(deps[n] for n in pure) or any(sorted(ds) != old_deps[n] for n, ds in deps.items()) or
            {n: sorted(ds) for n, ds in deps.items()} != record['dependencies']):
        raise ValueError('new/nonclosed assumption or original dependency mismatch')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^CHECK_LOCK_NORMAL_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('truncated/unbound final-name records')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    literal, transport = new_sources[1], new_sources[0]
    commands['source'] = [sys.executable, '-B', str(HERE.parent / 'elements-check-lock/check-source.py'), '--repo', str(work), '--coq', '.', '--literal', literal, '--transport', transport]
    commands['source-negative'] = [sys.executable, '-B', str(HERE.parent / 'elements-check-lock/test-source.py'), str(work), '.', literal, transport]
    for package in ['elements-finality', 'elements-lock']:
        positional = [] if package == 'elements-finality' else ['C/jet_elements_lock_literal.v']
        commands[package + '-negative'] = [sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.', *positional]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]
    if set(commands) != set(record['commands']):
        raise ValueError('missing final-name compiler/checker stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('wrong final-name command/flags/exit/log')
    tools = {'prepare.py': support.sha((HERE / 'prepare.py').read_bytes())}
    tools.update({p + '/' + n: support.sha((HERE.parent / p / n).read_bytes())
                  for p, names in [('elements-check-lock', ['check-source.py', 'test-source.py']),
                                   ('elements-finality', ['test-source.py']), ('elements-lock', ['test-source.py'])] for n in names})
    if record['tools_sha256'] != tools:
        raise ValueError('final-name checked-tool drift')
    for name in ['assumptions.log', 'contracts.log', 'ast.log', 'kernel.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived final-name evidence changed')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('final_check_lock_source', HERE.parent / 'elements-check-lock/check-source.py')
    source_gate.check(work, coq, coq / literal, coq / transport)
    return {'candidate': str(work), 'namespace': 'C', 'jets_checked': 5, 'fresh_modules': len(order),
            'result_types': len(results), 'definitions': len(definitions), 'closed_program_bridges': len(pure),
            'inherited_sources_byte_identical': len(inherited), 'success_failure_memory_contracts_retained': True,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
