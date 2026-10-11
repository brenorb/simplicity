"""Read-only exact compact-execution evidence review; no jet registration."""
import importlib.util
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent


def load(path):
    spec = importlib.util.spec_from_file_location('product_evidence', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def contracts(text, expected):
    if '...' in text or re.findall(r'(?m)^COMPACT_(TYPE|DEF) (\S+)$', text) != expected:
        raise ValueError('truncated/missing/reordered/duplicated contract')


def terminal(receipt):
    if (len(receipt['builds']) != 3 or len(receipt['kernel']) != 2
            or any(b['exit_code'] != 0 for b in receipt['builds'])
            or any(k['exit_code'] != 0 for k in receipt['kernel'])
            or receipt['drivers']['exit_code'] != 0):
        raise ValueError('failed or nonterminal verification')


def review():
    manifest = json.loads((ARCHIVE / 'manifest.json').read_text())
    receipt = json.loads((ARCHIVE / 'REVIEW.json').read_text())
    work = Path(manifest['scratch'])
    base = Path(manifest['dependency_coq'])
    common = load(ARCHIVE.parent / 'scalar-mul/review.py')
    parent = common.review()
    if parent['results'] != 17:
        raise ValueError('dependency reference changed')
    parent_manifest = json.loads((ARCHIVE.parent / 'scalar-mul/manifest.json').read_text())
    if (manifest['dependency_coq'] != parent_manifest['dependency_coq']
            or manifest['dependency_fingerprint'] != parent_manifest['dependency_fingerprint']):
        raise ValueError('different compiled dependency baseline')
    terminal(receipt)
    results, definitions = [], []
    for entry in manifest['modules']:
        source = ARCHIVE / (entry['file'] + '.source')
        if common.digest(source) != entry['sha256'] or source.read_bytes() != (work / entry['file']).read_bytes():
            raise ValueError('source/compiled archive drift')
        text = source.read_text()
        if (re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', text, re.M) != entry['results']
                or re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', text, re.M) != entry['definitions']):
            raise ValueError('source inventory drift')
        results += [entry['module'] + '.' + n for n in entry['results']]
        definitions += [entry['module'] + '.' + n for n in entry['definitions']]
    if (len(results), len(definitions)) != (19, 11):
        raise ValueError('unexpected closure')
    for name, digest in receipt['evidence_sha256'].items():
        if common.digest(work / name) != digest:
            raise ValueError('evidence drift: ' + name)
    for name in ['compact_assumptions.v', 'compact_contracts.v']:
        if (ARCHIVE / (name + '.source')).read_bytes() != (work / name).read_bytes():
            raise ValueError('driver drift')
    for name in ['compact_assumptions.err', 'compact_contracts.err']:
        if (work / name).read_bytes():
            raise ValueError('compiler diagnostics')
    deps = json.loads((ARCHIVE.parent / 'scalar-mul/REVIEW.json').read_text())['execution_dependencies']
    expected = {n: set(deps) if n in receipt['execution_results'] else set() for n in results}
    actual = common.assumptions((work / 'compact_assumptions.out').read_text(), expected)
    contracts((work / 'compact_contracts.out').read_text(),
              [('TYPE', n) for n in results] + [('DEF', n) for n in definitions])
    inherited = sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split())
    for kernel in receipt['kernel']:
        if common.digest(work / kernel['log']) != kernel['sha256']:
            raise ValueError('kernel evidence drift')
        context = inherited if kernel['context'] == 'inherited allowlist' else kernel['context']
        if not set(context) <= set(inherited):
            raise ValueError('new library axioms')
        common.kernel((work / kernel['log']).read_text(), context)
    return {'modules': 3, 'results': 19, 'closed_results': sum(not d for d in actual.values()),
            'definitions': 11, 'all_contracts_untruncated': True,
            'source_driver_dependency_kernel_evidence_match': True,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
