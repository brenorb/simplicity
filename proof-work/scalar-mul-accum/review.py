"""Read-only exact multiply-accumulate evidence check, not jet acceptance."""
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


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^ACCUM_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('contract report truncated/missing/reordered/duplicated')


def terminal(receipt):
    if (any(b['exit_code'] != 0 for b in receipt['builds'])
            or receipt['kernel']['exit_code'] != 0 or receipt['drivers']['exit_code'] != 0):
        raise ValueError('failed/nonterminal build or check')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    work = Path(manifest['scratch'])
    parent = ARCHIVE.parent / 'scalar-mul'
    common = load('umul128_review', parent / 'review.py')
    for name, digest in receipt['dependency_receipts'].items():
        if common.digest(parent / name) != digest:
            raise ValueError('dependency evidence changed')
    if common.review()['results'] != 17:
        raise ValueError('underlying product/helper closure changed')
    terminal(receipt)
    results, definitions = [], []
    for module in manifest['modules']:
        path = ARCHIVE / (module['file'] + '.source')
        if common.digest(path) != module['sha256'] or path.read_bytes() != (work / module['file']).read_bytes():
            raise ValueError('compiled/archived source mismatch')
        text = path.read_text()
        if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != module['results']
                or re.findall(r'^Definition\s+(\w+)', text, re.M) != module['definitions']):
            raise ValueError('source inventory drift')
        results += [module['module'] + '.' + n for n in module['results']]
        definitions += [module['module'] + '.' + n for n in module['definitions']]
    if (len(results), len(definitions)) != (11, 8):
        raise ValueError('unexpected helper closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence changed: ' + name)
    for name in ['accum_mul_assumptions.v', 'accum_mul_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived driver changed')
    for name in ['accum_mul_assumptions.err', 'accum_mul_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    inherited = json.loads((parent / 'REVIEW.json').read_text())['execution_dependencies']
    expected = {n: set(inherited) if n in receipt['execution_results'] else set() for n in results}
    deps = common.assumptions((work / 'accum_mul_assumptions.out').read_text(), expected)
    contracts((work / 'accum_mul_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    evidence = receipt['kernel']
    if common.digest(work / evidence['log']) != evidence['sha256']:
        raise ValueError('kernel output changed')
    context = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
    common.kernel((work / evidence['log']).read_text(), context)
    return {'new_modules': 2, 'new_results': 11, 'closed_results': sum(not d for d in deps.values()),
            'definitions': 8, 'parent_results_revalidated': 17, 'kernel_context_matches': len(context),
            'sources_and_complete_type_definition_dependency_evidence_match': True,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
