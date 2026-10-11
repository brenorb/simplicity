"""Read-only evidence for the actual first and second stage execution; no public acceptance."""
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
        raise ValueError('two-stage body prefix is not public equivalence acceptance')


def inventory(text, entry):
    explicit = [n for n in entry['definitions'] if n not in entry['generated_definitions']]
    if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
            or re.findall(r'^(?:Definition|Fixpoint|Record|Inductive)\s+(\w+)', text, re.M) != explicit):
        raise ValueError('source inventory drift')


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^TWO_STAGES_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicate contract')


def review():
    parent = load('two_stages_execution_reference', ARCHIVE.parent / 'scalar-reduce512-bounds/review.py')
    if parent.review()['results'] != 14:
        raise ValueError('original execution prerequisite drift')
    common = load('two_stages_common', ARCHIVE.parent / 'scalar-mul/review.py')
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
    if (len(manifest['modules']), len(results), len(definitions)) != (8, 42, 34):
        raise ValueError('unexpected two-stage closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['two_stages_assumptions.v', 'two_stages_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['two_stages_assumptions.err', 'two_stages_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    representation = {'MulC.jet_sx_forget_cells.' + n for n in
                      ['forget_region_ok', 'rep_forget_cells', 'rep_forget_after']}
    representation_deps = set(deps) - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    if (set(receipt['representation_results']) != representation
            or set(receipt['representation_dependencies']) != representation_deps):
        raise ValueError('representation dependency classification drift')
    expected = {n: set(deps) if n in receipt['execution_results'] else
                representation_deps if n in representation else set() for n in results}
    actual = common.assumptions((work / 'two_stages_assumptions.out').read_text(), expected)
    contracts((work / 'two_stages_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    kernel = receipt['kernel']
    if common.digest(work / kernel['log']) != kernel['sha256']:
        raise ValueError('kernel evidence drift')
    inherited = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / kernel['log']).read_text(), inherited)
    return {'modules': 8, 'results': 42, 'closed_results': sum(not x for x in actual.values()),
            'definitions': 34, 'actual_original_first_two_prefixes_execute': True,
            'typed_checkpoint_temp_memory_and_guards_discharged': True,
            'all_second_stage_machine_outputs_and_narrowing_accounted_for': True,
            'source_driver_dependency_kernel_evidence_matches': True,
            'whole_reduce512_numeric_modulo_identity': False,
            'complete_function_entry_free': False,
            'public_jet_equivalence': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
