"""Read-only evidence for the original in-place scalar multiplication caller body; no public acceptance."""
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
    if '...' in text or re.findall(r'(?m)^FRESH_CALLER_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicate contract')


def classifications(receipt, results, deps):
    execution = ["MulC.jet_secp_scalar_mul512_fresh.eval_scalar_mul512_fresh","MulC.jet_secp_scalar_mul512_fresh.eval_scalar_mul512_fresh_product","MulC.jet_secp_product_reduce_bridge.eval_product_then_reduce","MulC.jet_secp_scalar_mul_caller_body.exec_scalar_mul_product_call","MulC.jet_secp_scalar_mul_caller_body.exec_scalar_mul_reduction_call","MulC.jet_secp_scalar_mul_caller_body.exec_scalar_mul_caller_body_inplace"]
    representation = ["MulC.jet_sx_u64_transport.region_u64_transport","MulC.jet_secp_product_reduce_bridge.product_reduce_entry_rep"]
    if (set(receipt['execution_results']) != set(execution)
            or set(receipt['representation_results']) != set(representation)):
        raise ValueError('execution/representation classification drift')
    rep_deps = set(deps) - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    return {n: set(deps) if n in execution else rep_deps if n in representation else set()
            for n in results}


def review():
    parent = load('final_execution_reference', ARCHIVE.parent / 'scalar-reduce512-final/review.py')
    if parent.review()['results'] != 42:
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
    if (len(manifest['modules']), len(results), len(definitions)) != (4, 22, 8):
        raise ValueError('unexpected in-place caller-body closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['fresh_caller_assumptions.v', 'fresh_caller_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['fresh_caller_assumptions.err', 'fresh_caller_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    expected = classifications(receipt, results, deps)
    actual = common.assumptions((work / 'fresh_caller_assumptions.out').read_text(), expected)
    contracts((work / 'fresh_caller_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    if sum(not x for x in actual.values()) != 14:
        raise ValueError('closed-result classification drift')
    return {'modules': 4, 'results': 22, 'closed_results': 14, 'definitions': 8,
            'uninitialized_product_output_supported': True,
            'current_memory_product_reduce_representation_discharged': True,
            'original_scalar_mul_body_r_equals_a': True,
            'exact_product_modulo_canonical_order': True,
            'outside_region_framing': True,
            'source_driver_dependency_kernel_evidence_matches': True,
            'complete_caller_function_entry_alloc_free': False,
            'square_shared_input_alias': False,
            'public_jet_equivalence': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
