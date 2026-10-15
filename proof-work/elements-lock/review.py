"""Validate lock literal-program and original-C proof evidence, not admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('lock_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    record = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq, literal = work / 'Coq', work / 'Proof/jet_elements_lock_literal.v'
    prior_path = HERE.parent / 'elements-finality/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    order = ['C.jet_elements_write32s_exec', 'C.jet_elements_write32s_layout',
             'C.jet_elements_hash_write', 'C.jet_elements_hash_getters',
             'C.jet_elements_tx_field_set', 'C.jet_elements_is_final_spec',
             'C.jet_elements_is_final_local', 'C.jet_elements_lock_exec',
             'C.jet_elements_lock_spec', 'C.jet_elements_lock_local']
    literal_module = 'LockLiteral.jet_elements_lock_literal'
    modules = order + [literal_module]
    if (record['fresh_modules'] != order or record['modules'] != modules or record['namespace'] != 'LockLiteral' or
            record['normal_registration'] is not False or record['coverage_added'] != 0 or
            record['full_acceptance'] is not False or str(base) != prior['candidate'] or
            record['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong lock literal/original-C preparation scope')
    if (support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
            support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256'] or
            record['candidate_input_sha256'] != prior['candidate_input_sha256'] or
            support.index_hash() != record['staged_patch_sha256']):
        raise ValueError('lock inherited source/index identity changed')
    results, definitions = [], []
    for module in modules:
        name = module.replace('.', '/') + '.v'
        path = literal if module == literal_module else coq / name
        if module != literal_module and (path.read_bytes() != (base / 'Coq' / name).read_bytes() or
                                       path.read_bytes() != (REPO / 'Coq' / name).read_bytes()):
            raise ValueError('unreviewed inherited C proof edit')
        archive = HERE / 'source' / (module.split('.')[-1] + '.v.source')
        obj = path.with_suffix('.vo')
        if (path.read_bytes() != archive.read_bytes() or obj.is_symlink() or
                record['source_sha256'].get(module) != support.sha(path.read_bytes()) or
                record['object_sha256'].get(module) != support.sha(obj.read_bytes())):
            raise ValueError('source/archive/object mismatch')
        code = support.safe_source(path.read_text(), module)
        results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
    pure = [literal_module + '.' + n for n in ['elements_parse_lock_literal_matches', 'elements_lock_literal_program_matches']]
    if (record['results'] != results or record['definitions'] != definitions or record['pure_results'] != pure or
            set(record['source_sha256']) != set(modules) or set(record['object_sha256']) != set(modules)):
        raise ValueError('incomplete lock statement/source/object inventory')
    flags = ['-Q', str(work / 'Proof'), 'LockLiteral']
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands['literal'] = ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(literal)]
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
    commands['source'] = [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.', '--literal', str(literal)]
    commands['source-negative'] = [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal)]
    commands['ast'] = ['bash', 'C/check-elements-jets-generation.sh']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', 'C.jet_elements_lock_local', literal_module]
    if set(commands) != set(record['commands']):
        raise ValueError('missing lock compiler/checker stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('wrong lock compiler/checker command/exit/log')
    if set(record['tools_sha256']) != {'check.py', 'check-source.py', 'test-source.py'}:
        raise ValueError('incomplete lock tool binding')
    for name, digest in record['tools_sha256'].items():
        if support.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('checked lock tool changed')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
            any(deps[n] for n in pure) or {n: sorted(ds) for n, ds in deps.items()} != record['dependencies']):
        raise ValueError('new lock assumptions/nonclosed bridges')
    for suffix in ['height', 'time']:
        if deps[literal_module + '.elements_tx_lock_' + suffix + '_literal_local_spec'] != deps[
                'C.jet_elements_lock_local.elements_tx_lock_' + suffix + '_local_spec']:
            raise ValueError('literal C endpoint assumptions differ from original')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^LOCK_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('truncated/unbound lock record')
    for name in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived lock evidence changed')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    source_gate = support.load('lock_review_source_gate', HERE / 'check-source.py')
    source_gate.check(work, coq, literal)
    return {'jets': ['simplicity_tx_lock_height', 'simplicity_tx_lock_time'], 'candidate': str(work),
            'fresh_C_modules': len(order), 'new_literal_modules': 1, 'closed_source_bridges': len(pure),
            'full_result_types': len(results), 'full_definitions': len(definitions),
            'source_kernel_AST_checks': True, 'coverage_added': 0,
            'normal_registration': False, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
