"""Read-only contract inventory/printing reconciliation, not proof acceptance.

Deep supplements recover truncated non-diagnostic printed terms. Retained
ellipsis fragments are only printing diagnostics, not equality certificates.
Large execution trees retain checked source/run/shape lemmas; printing a tree
is not a separate correctness proof.
"""
from collections import Counter
import hashlib
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


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(path):
    return [tuple(line.split()) for line in path.read_text().splitlines()
            if line.strip() and not line.startswith('#')]


def compact(text):
    return re.sub(r'\s+', '', text)


def review():
    receipt = json.loads((ARCHIVE / 'ASSEMBLY.json').read_text())
    base = Path(receipt['baseline']) / 'Coq/C'
    candidate = Path(receipt['candidate']) / 'Coq/C'
    work = candidate.parent.parent
    results = [('C.' + item['name'], name) for item in receipt['modules'] for name in item['results']]
    definitions = [('C.' + item['name'], name) for item in receipt['modules'] for name in item['definitions']]
    old_results = inventory(base / 'jet_public_theorems.txt')
    old_definitions = inventory(base / 'jet_contract_definitions.txt')
    if (inventory(candidate / 'jet_public_theorems.txt') != old_results + results
            or inventory(candidate / 'jet_contract_definitions.txt') != old_definitions + definitions):
        raise ValueError('contract inventory is not exact append-only extension')
    names = {n for _, n in results + definitions}
    old_names = {n for _, n in old_results + old_definitions}
    if names & old_names != {'u128_field'}:
        raise ValueError('unexpected new/inherited printed names conflict')
    parser = load('contract_chunks', ARCHIVE.parent / 'ge-negate/review-full-snapshots.py')
    baseline = (base / 'jet_contracts.expected').read_text()
    ordinary = (candidate / 'jet_contracts.expected').read_text()
    chunks = parser.chunks(ordinary, old_names | names, inherited_print_context=True)
    def is_new(name, text):
        if name == 'u128_field':
            # The sorted import context keeps the inherited jet_u128_fields
            # version unqualified and qualifies this one new secp definition.
            # Distinguish exact headers; do not drop arbitrary namespaces.
            if text.startswith('jet_secp_u128_shift64_expr.u128_field ='):
                return True
            if text.startswith('u128_field ='):
                return False
            raise ValueError('unexpected u128_field printing identity')
        return name in names
    inherited = ''.join(text for name, text in chunks if not is_new(name, text))
    if inherited != baseline:
        raise ValueError('inherited contracts changed; inspect the exact diff')
    added = [(name, text) for name, text in chunks if is_new(name, text)]
    expected = results + definitions
    if [name for name, _ in added] != [name for _, name in expected]:
        raise ValueError('new contract inventory reordered/missing/extra')
    if len(added) != 298:
        raise ValueError('unexpected contract record count')
    deep_path = work / 'scalar-deep-contracts.out'
    pinned_path = ARCHIVE / 'NORMAL-CONTRACT-REVIEW.json'
    if pinned_path.exists():
        pinned = json.loads(pinned_path.read_text())
        for path, field in [(work / 'scalar_deep_contracts.v', 'driver_sha256'),
                            (deep_path, 'deep_sha256'),
                            (candidate / 'jet_contracts.expected', 'candidate_contract_snapshot_sha256')]:
            if sha(path) != pinned[field]:
                raise ValueError('reviewed contract output/driver drift')
    deep_text = deep_path.read_text()
    if (work / 'scalar-deep-contracts.err').read_bytes() or '...' in deep_text:
        raise ValueError('deep report diagnostic or truncation')
    markers = list(re.finditer(r'(?m)^SCALAR_(TYPE|DEF) (\S+)\n', deep_text))
    wanted_deep = [('TYPE', mod + '.' + name) for mod, name in results]
    wanted_deep += [('DEF', mod + '.' + name) for mod, name in definitions if not name.endswith('_tree')]
    if [(m[1], m[2]) for m in markers] != wanted_deep:
        raise ValueError('deep supplement inventory drift')
    deep = {(m[1], m[2]): deep_text[m.end():markers[i + 1].start() if i + 1 < len(markers) else len(deep_text)]
            for i, m in enumerate(markers)}
    if len(deep) != len(wanted_deep):
        raise ValueError('duplicate deep record')
    supplements, diagnostic_trees = [], []
    for i, ((module, name), (_, text)) in enumerate(zip(expected, added)):
        kind = 'TYPE' if i < len(results) else 'DEF'
        key = module + '.' + name
        if kind == 'DEF' and name.endswith('_tree'):
            diagnostic_trees.append(key)
            continue
        current, expanded = compact(text), compact(deep[(kind, key)])
        if current == expanded:
            continue
        position = 0
        fragments = current.split('...')
        for j, fragment in enumerate(fragments):
            offset = (len(expanded) - len(fragment) if j == len(fragments) - 1
                      and expanded.endswith(fragment) else expanded.find(fragment, position))
            if offset < position or (j == 0 and offset != 0):
                raise ValueError('non-print-depth difference: ' + key)
            position = offset + len(fragment)
        if '...' not in current or position != len(expanded):
            raise ValueError('unexpected contract difference: ' + key)
        supplements.append(key)
    return {'candidate': str(work), 'inherited_contracts_byte_identical': True,
            'new_types': len(results), 'new_definitions': len(definitions),
            'all_new_non_diagnostic_terms_untruncated': True,
            'deep_ellipsis_supplements': supplements,
            'execution_tree_prints_diagnostic_only': diagnostic_trees,
            'source_and_execution_shape_proofs_required': True,
            'driver_sha256': sha(work / 'scalar_deep_contracts.v'),
            'deep_sha256': sha(deep_path),
            'candidate_contract_snapshot_sha256': sha(candidate / 'jet_contracts.expected'),
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
