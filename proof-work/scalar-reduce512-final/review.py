"""Read-only evidence for the complete original reduce512 helper numeric execution; no public acceptance."""
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def terminal(receipt):
    if any(receipt[k]['exit_code'] != 0 for k in ['build', 'kernel', 'drivers']):
        raise ValueError('failed/nonterminal verification')
    if receipt['full_acceptance'] or receipt['checkout_coverage_added'] != 0:
        raise ValueError('complete helper is not public equivalence acceptance')


def inventory(text, entry):
    explicit = [n for n in entry['definitions'] if n not in entry['generated_definitions']]
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
            or re.findall(r'^(?:Definition|Fixpoint|Record|Inductive)\s+(\w+)', text, re.M) != explicit):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^FINAL_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicate contract')


def classifications(receipt, results, deps):
    execution = ["MulC.jet_secp_reduce512_final_exec.exec_typed_final_suffix","MulC.jet_secp_reduce512_body_numeric.exec_reduce512_body_numeric","MulC.jet_secp_reduce512_function_numeric.eval_reduce512_numeric_owned","MulC.jet_secp_reduce512_function_numeric.eval_reduce512_numeric_owned_loads"]
    representation = ["MulC.jet_sx_revalue_cells.region_ok_revalue","MulC.jet_sx_revalue_cells.rep_change_head","MulC.jet_sx_revalue_cells.region_ok_revalue_u64","MulC.jet_secp_reduce512_final_checkpoint.third_checkpoint_rep"]
    if (set(receipt['execution_results']) != set(execution)
            or set(receipt['representation_results']) != set(representation)):
        raise ValueError('execution/representation classification drift')
    rep_deps = set(deps) - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    return {n: set(deps) if n in execution else rep_deps if n in representation else set()
            for n in results}


def review():
    parent = load('final_execution_reference', ARCHIVE.parent / 'scalar-reduce512-three-stages/review.py')
    if parent.review()['results'] != 30:
        raise ValueError('original execution prerequisite drift')
    common = load('final_common', ARCHIVE.parent / 'scalar-mul/review.py')
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    terminal(receipt)
    work = Path(manifest['scratch'])
    results, definitions = [], []
    for entry in manifest['modules']:
        path = ARCHIVE / (entry['file'] + '.source')
        if common.digest(path) != entry['sha256'] or path.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('archive/compiled source drift')
        inventory(path.read_text(), entry)
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(manifest['modules']), len(results), len(definitions)) != (8, 42, 26):
        raise ValueError('unexpected complete-helper closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['final_assumptions.v', 'final_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['final_assumptions.err', 'final_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    expected = classifications(receipt, results, deps)
    actual = common.assumptions((work / 'final_assumptions.out').read_text(), expected)
    contracts((work / 'final_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    if sum(not x for x in actual.values()) != 34:
        raise ValueError('closed-result classification drift')
    return {'modules': 8, 'results': 42, 'closed_results': 34,
            'definitions': 26, 'actual_original_whole_body_executes': True,
            'whole_reduce512_numeric_modulo_identity': True,
            'complete_function_entry_alloc_return_free': True,
            'final_memory_loads_after_cleanup': True,
            'source_driver_dependency_kernel_evidence_matches': True,
            'public_jet_equivalence': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
