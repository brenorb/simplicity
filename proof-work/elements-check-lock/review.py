"""Revalidate check-lock proof, assertion/failure semantics and kernel evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('check_lock_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    record = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-timelock-normal/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    order = ['C.jet_elements_bool_wrapper', 'C.jet_elements_prim_sem', 'C.jet_elements_tx_field_set',
             'C.jet_elements_is_final_spec', 'C.jet_elements_is_final_local', 'C.jet_elements_lock_exec',
             'C.jet_elements_lock_spec', 'C.jet_elements_lock_local', 'C.jet_elements_check_lock',
             'C.jet_elements_lock_literal']
    proof_modules = ['CheckLockReview.jet_application_partial_transport', 'CheckLockReview.jet_elements_check_lock_literal']
    roots, modules = ['C.jet_elements_check_lock', *proof_modules], order + proof_modules
    references = ['C.jet_elements_sequence_literal.application_jet_local_spec_sep_pointwise']
    pure = [proof_modules[1] + '.elements_check_lock_literal_program_matches']
    if (record['namespace'] != 'CheckLockReview' or record['fresh_modules'] != order or
            record['proof_modules'] != proof_modules or record['roots'] != roots or
            record['pure_results'] != pure or record['reference_results'] != references or
            record['normal_registration'] is not False or record['coverage_added'] != 0 or
            record['full_acceptance'] is not False or str(base) != prior['candidate'] or
            record['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong check-lock scope/source base/transport references')
    if (record['candidate_input_sha256'] != prior['candidate_input_sha256'] or
            support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
            support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256'] or
            support.index_hash() != record['staged_patch_sha256']):
        raise ValueError('check-lock source-copy/index identity changed')
    paths = {m: work / 'Proof' / (m.split('.')[-1] + '.v') for m in proof_modules}
    paths.update({m: coq / (m.replace('.', '/') + '.v') for m in order})
    results, definitions = [], []
    for module in modules:
        path = paths[module]
        if module in order and path.read_bytes() != (base / 'Coq' / path.relative_to(coq)).read_bytes():
            raise ValueError('inherited check-lock C proof changed')
        archive = HERE / 'source' / (module.split('.')[-1] + '.v.source')
        obj = path.with_suffix('.vo')
        if (path.read_bytes() != archive.read_bytes() or obj.is_symlink() or
                record['source_sha256'].get(module) != support.sha(path.read_bytes()) or
                record['object_sha256'].get(module) != support.sha(obj.read_bytes())):
            raise ValueError('check-lock source/archive/object mismatch')
        code = support.safe_source(path.read_text(), module)
        results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
    if (record['results'] != results or record['definitions'] != definitions or
            set(record['source_sha256']) != set(modules) or set(record['object_sha256']) != set(modules)):
        raise ValueError('incomplete check-lock public/source/object inventory')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results + references) or any(not ds <= support.SIX for ds in deps.values()) or
            any(deps[n] for n in pure) or deps[proof_modules[0] + '.application_jet_partial_spec_pointwise'] != deps[references[0]] or
            {n: sorted(ds) for n, ds in deps.items()} != record['dependencies']):
        raise ValueError('new assumptions/nonclosed program bridge/transport-reference mismatch')
    for suffix in ['height', 'time']:
        if deps[proof_modules[1] + '.elements_check_lock_' + suffix + '_literal_local_spec'] != deps[
                'C.jet_elements_check_lock.elements_check_lock_' + suffix + '_local_spec']:
            raise ValueError('new endpoint assumptions differ from original')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^CHECK_LOCK_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete check-lock deep reports')
    flags = ['-Q', str(work / 'Proof'), 'CheckLockReview']
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({m: ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(paths[m])] for m in proof_modules})
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    literal, transport = paths[proof_modules[1]], paths[proof_modules[0]]
    commands['source'] = [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.', '--literal', str(literal), '--transport', str(transport)]
    commands['source-negative'] = [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal), str(transport)]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', *roots]
    if set(record['commands']) != set(commands):
        raise ValueError('missing check-lock compile/source/kernel stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('wrong check-lock command/flags/exit/log')
    tools = ['check.py', 'check-source.py', 'test-source.py']
    if record['tools_sha256'] != {n: support.sha((HERE / n).read_bytes()) for n in tools}:
        raise ValueError('check-lock source/replay tool drift')
    for name in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived check-lock evidence changed')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('check_lock_review_source', HERE / 'check-source.py')
    source_gate.check(work, coq, literal, transport)
    return {'jets': ['simplicity_check_lock_height', 'simplicity_check_lock_time'], 'candidate': str(work),
            'fresh_C_modules': len(order), 'new_proof_modules': len(proof_modules),
            'full_result_types': len(results), 'full_definitions': len(definitions),
            'closed_program_bridges': 1, 'transport_matches_inherited_context': True,
            'success_failure_memory_contract_retained': True, 'recursive_kernel_and_exact_AST': True,
            'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
