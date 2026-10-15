"""Verify fresh finality proof/source/kernel receipts; not normal admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('finality_review_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    record = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(record['candidate']), Path(record['base_candidate'])
    coq = work / 'Coq'
    prior_path = HERE.parent / 'elements-direct-getters-normal/PREPARATION.json'
    prior = json.loads(prior_path.read_text())
    roots = ['C.jet_elements_is_final_spec', 'C.jet_elements_is_final_local']
    order = ['C.jet_elements_is_final_spec', 'C.jet_elements_write32s_exec',
             'C.jet_elements_write32s_layout', 'C.jet_elements_hash_write',
             'C.jet_elements_hash_getters', 'C.jet_elements_tx_field_set',
             'C.jet_elements_is_final_local']
    if (record['roots'] != roots or record['fresh_modules'] != order or
            record['normal_registration'] is not False or record['coverage_added'] != 0 or
            record['full_acceptance'] is not False or str(base) != prior['candidate'] or
            record['prior_preparation_sha256'] != support.sha(prior_path.read_bytes())):
        raise ValueError('wrong finality preparation scope/base')
    if (support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
            support.inputs.fingerprint(base / 'Coq', base) != record['base_input_sha256'] or
            record['base_input_sha256'] != prior['candidate_input_sha256'] or
            record['candidate_input_sha256'] != record['base_input_sha256']):
        raise ValueError('finality source-copy identity changed')
    if support.index_hash() != record['staged_patch_sha256']:
        raise ValueError('original staged work changed')
    results, definitions = [], []
    for module in order:
        name = module.replace('.', '/') + '.v'
        source, obj = coq / name, (coq / name).with_suffix('.vo')
        archived = HERE / 'source' / (module.removeprefix('C.') + '.v.source')
        if (source.read_bytes() != (base / 'Coq' / name).read_bytes() or
                source.read_bytes() != (REPO / 'Coq' / name).read_bytes() or
                source.read_bytes() != archived.read_bytes() or obj.is_symlink() or
                record['sources_sha256'].get(module) != support.sha(source.read_bytes()) or
                record['objects_sha256'].get(module) != support.sha(obj.read_bytes())):
            raise ValueError('finality source/object/archive identity changed')
        code = support.safe_source(source.read_text(), module)
        results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
        definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
    if record['results'] != results or record['definitions'] != definitions:
        raise ValueError('incomplete finality statement/definition inventory')
    if set(record['sources_sha256']) != set(order) or set(record['objects_sha256']) != set(order):
        raise ValueError('incomplete finality fresh-source/object inventory')
    commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
    commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['contracts', 'assumptions']})
    commands['source'] = [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.']
    commands['source-negative'] = [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.']
    commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots]
    if set(commands) != set(record['commands']):
        raise ValueError('missing fresh-compile/source/kernel command')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('wrong finality command/flags/exit/log evidence')
    for name, digest in record['tools_sha256'].items():
        if support.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('checked finality tool drift')
    if set(record['tools_sha256']) != {'prepare.py', 'check-source.py', 'test-source.py'}:
        raise ValueError('missing finality tool binding')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
            {n: sorted(ds) for n, ds in deps.items()} != record['dependencies']):
        raise ValueError('new/unreviewed finality assumptions')
    report = (work / 'contracts.log').read_text()
    if ('...' in report or re.search(r'\?[A-Za-z]', report) or
            re.findall(r'(?m)^FINALITY_(TYPE|DEF) (\S+)$', report) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete deep finality records')
    for name in ['contracts.log', 'assumptions.log', 'kernel.log', 'source.log', 'source-negative.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived finality evidence differs')
    support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
    ast = json.loads((HERE / 'AST.json').read_text())
    if (ast['candidate'] != str(work) or ast['candidate_input_sha256'] != record['candidate_input_sha256'] or
            ast['command'] != ['bash', 'C/check-elements-jets-generation.sh'] or ast['exit_code'] != 0 or
            ast['log_sha256'] != support.sha((work / 'ast.log').read_bytes()) or
            (HERE / 'ast.log').read_bytes() != (work / 'ast.log').read_bytes() or
            ast['ast_sha256'] != support.sha((coq / 'C/jets_elements.v').read_bytes())):
        raise ValueError('Elements AST regeneration evidence differs')
    source_gate = support.load('finality_review_source_gate', HERE / 'check-source.py')
    source_gate.check(work, coq)
    return {'jet': 'simplicity_tx_is_final', 'candidate': str(work),
            'fresh_modules': len(order), 'full_result_types': len(results),
            'full_definitions': len(definitions), 'canonical_recursive_program_reviewed': True,
            'recursive_kernel_checked': True, 'exact_elements_ast': True,
            'coverage_added': 0, 'normal_registration': False, 'full_acceptance': False}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
