"""Reconcile every normal-C dependency set with pinned OriginalC evidence."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rows(path):
    result = [tuple(line.split()) for line in path.read_text().splitlines()
              if line.strip() and not line.startswith('#')]
    if any(len(row) != 2 for row in result) or len(set(result)) != len(result):
        raise ValueError('malformed/duplicate result inventory')
    return result


def snapshot(path):
    result = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        name, dependencies = line.split(' : ', 1)
        if name in result:
            raise ValueError('duplicate dependency record')
        result[name] = [] if dependencies == 'closed' else dependencies.split(', ')
        if len(set(result[name])) != len(result[name]):
            raise ValueError('duplicate axiom')
    return result


def review():
    receipt = json.loads((ARCHIVE / 'ASSEMBLY.json').read_text())
    base, candidate = Path(receipt['baseline']) / 'Coq', Path(receipt['candidate']) / 'Coq'
    assembler = load('scalar_assembler', ARCHIVE / 'assemble-candidate.py')
    planned = assembler.plan(Path(receipt['baseline']), Path(receipt['work']))
    modules = [{k: v for k, v in item.items() if k != 'text'} for item in planned['modules']]
    if modules != receipt['modules']:
        raise ValueError('assembly source inventory drift')
    for name, digest in receipt['added_file_hashes'].items():
        if sha(candidate / name) != digest:
            raise ValueError('candidate source/gate drift')
    for name, digests in receipt['metadata'].items():
        if sha(candidate / name) != digests['candidate_sha256'] or sha(base / name) != digests['baseline_sha256']:
            raise ValueError('candidate infrastructure drift')
    inherited = sorted(base.rglob('*.v'))
    for path in inherited:
        if path.read_bytes() != (candidate / path.relative_to(base)).read_bytes():
            raise ValueError('inherited source drift')
    expected_sources = {path.relative_to(base) for path in inherited}
    expected_sources.update(Path('C') / (item['name'] + '.v') for item in modules)
    if {path.relative_to(candidate) for path in candidate.rglob('*.v')} != expected_sources:
        raise ValueError('unexpected candidate source module')
    old_rows = rows(base / 'C/jet_public_theorems.txt')
    added_rows = [('C.' + item['name'], n) for item in modules for n in item['results']]
    if rows(candidate / 'C/jet_public_theorems.txt') != old_rows + added_rows:
        raise ValueError('result inventory is not exact append-only extension')
    original = {}
    parser = load('strict_dependencies', ARCHIVE.parent / 'gej-predicate/review-preliminary.py')
    for directory in ['scalar-next', 'scalar-reduce', 'scalar-set', 'scalar-reader',
                      'scalar-reader-lifecycle', 'scalar-reader-zero', 'scalar-public-entry', 'scalar-zero']:
        archive = ARCHIVE.parent / directory
        manifest = json.loads((archive / 'manifest.json').read_text())
        entries = manifest.get('modules', [manifest] if 'file' in manifest else [])
        wanted = {'OriginalC.' + item['file'][:-2] + '.' + n for item in entries for n in item['results']}
        if directory == 'scalar-next':
            historical = json.loads((archive / 'ASSUMPTION-REVIEW.json').read_text())
            report, pinned = 'assumptions-review.out', historical['log_hashes']['assumptions-review.out']
        else:
            matches = [(n, h) for n, h in manifest['output_hashes'].items() if n.endswith('assumptions.out')]
            if len(matches) != 1:
                raise ValueError('ambiguous historical dependency output')
            report, pinned = matches[0]
        actual_path = Path(receipt['work']) / report
        if sha(actual_path) != pinned:
            raise ValueError('historical dependency report drift')
        parsed = parser.assumptions(actual_path, wanted)
        if set(original) & set(parsed):
            raise ValueError('duplicate historical result')
        original.update(parsed)
    expected = {mod + '.' + n: sorted(original['OriginalC.' + mod[2:] + '.' + n]) for mod, n in added_rows}
    old, new = snapshot(base / 'C/jet_assumptions.expected'), snapshot(candidate / 'C/jet_assumptions.expected')
    if set(old) != {mod + '.' + n for mod, n in old_rows}:
        raise ValueError('baseline dependency inventory mismatch')
    if any(new.get(name) != dependencies for name, dependencies in old.items()):
        raise ValueError('inherited dependencies changed')
    actual_added = {name: sorted(deps) for name, deps in new.items() if name not in old}
    if actual_added != expected:
        raise ValueError('new per-result dependencies differ from checked OriginalC results')
    return {'candidate': str(candidate.parent), 'inherited_results_unchanged': len(old),
            'added_results': len(expected), 'added_closed': sum(not a for a in expected.values()),
            'total_results': len(new), 'exact_namespace_transport_dependencies': True,
            'candidate_assumptions_sha256': sha(candidate / 'C/jet_assumptions.expected'),
            'all_sources_and_infrastructure_unchanged': True,
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
