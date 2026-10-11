"""Exact normal namespace/source/contract/dependency review, not acceptance.

The optional preparation operation only installs the freshly parsed, exactly
reconciled assumption extension. It does not accept it: full check-jets must
subsequently compare all results and independently kernel-check the candidate.
"""
import argparse
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
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


def inputs():
    receipt = json.loads((ARCHIVE / 'ASSEMBLY.json').read_text())
    base, candidate = Path(receipt['baseline']) / 'Coq', Path(receipt['candidate']) / 'Coq'
    assembler = load('scalar_integration_assembly', ARCHIVE / 'assemble-candidate.py')
    planned = assembler.plan(base.parent)
    modules = [{k: v for k, v in e.items() if k != 'text'} for e in planned['modules']]
    if modules != receipt['modules']:
        raise ValueError('assembly provenance/inventory drift')
    accepted = json.loads((ARCHIVE.parent / 'scalar-zero/ACCEPTANCE.json').read_text())
    if (Path(accepted['candidate']).resolve() != base.parent or accepted['exit_code'] != 0
            or accepted['audit_input_sha256'] != receipt['baseline_fingerprint']
            or sha(Path(accepted['log'])) != accepted['log_sha256']):
        raise ValueError('parent terminal acceptance evidence changed')
    for name, digest in receipt['added_file_hashes'].items():
        if sha(candidate / name) != digest:
            raise ValueError('new source or source gate drift: ' + name)
    for name, digests in receipt['metadata'].items():
        if sha(candidate / name) != digests['candidate_sha256'] or sha(base / name) != digests['baseline_sha256']:
            raise ValueError('infrastructure drift: ' + name)
    inherited = sorted(base.rglob('*.v'))
    for path in inherited:
        if path.read_bytes() != (candidate / path.relative_to(base)).read_bytes():
            raise ValueError('inherited source drift')
    expected_sources = {p.relative_to(base) for p in inherited}
    expected_sources.update(Path('C') / (e['name'] + '.v') for e in modules)
    if {p.relative_to(candidate) for p in candidate.rglob('*.v')} != expected_sources:
        raise ValueError('missing/unregistered source module')
    if (base / 'C/jet_coqchk_axioms.expected').read_bytes() != (candidate / 'C/jet_coqchk_axioms.expected').read_bytes():
        raise ValueError('kernel axiom allowlist changed')
    return receipt, base, candidate


def dependencies(receipt, base, candidate):
    parser = load('scalar_strict_dependencies', ARCHIVE.parent / 'gej-predicate/review-preliminary.py')
    expected = {}
    for family in {e['family'] for e in receipt['modules']}:
        directory = ARCHIVE.parent / family
        manifest = json.loads((directory / 'manifest.json').read_text())
        work = Path(manifest['scratch'])
        historical_modules = manifest['modules']
        wanted = {e.get('module', 'OriginalC.' + e['file'][:-2]) + '.' + n
                  for e in historical_modules for n in e['results']}
        if family == 'scalar-next':
            historical = json.loads((directory / 'ASSUMPTION-REVIEW.json').read_text())
            name, digest = 'assumptions-review.out', historical['log_hashes']['assumptions-review.out']
        else:
            matches = [(n, h) for n, h in manifest['output_hashes'].items() if n.endswith('assumptions.out')]
            if len(matches) != 1:
                raise ValueError('ambiguous historical dependency output')
            name, digest = matches[0]
        if sha(work / name) != digest:
            raise ValueError('historical dependency output changed')
        old = parser.assumptions(work / name, wanted)
        for entry in receipt['modules']:
            if entry['family'] != family:
                continue
            for name in entry['results']:
                key = 'C.' + entry['name'] + '.' + name
                if key in expected:
                    raise ValueError('duplicate dependency key')
                expected[key] = old[entry['original_module'] + '.' + name]
    work = candidate.parent
    if (work / 'new-assumptions.err').read_bytes():
        raise ValueError('new dependency diagnostics')
    actual = parser.assumptions(work / 'new-assumptions.out', set(expected))
    if actual != expected:
        raise ValueError('normal dependencies differ from checked namespace archives')
    snapshots = load('scalar_snapshot_parser', ARCHIVE.parent / 'ge-negate/review-full-snapshots.py')
    inherited = snapshots.assumptions(base / 'C/jet_assumptions.expected')
    if set(expected) & set(inherited):
        raise ValueError('new/inherited dependency collision')
    combined = {**inherited, **{n: sorted(v) for n, v in expected.items()}}
    wanted_text = ''.join(n + ' : ' + (', '.join(v) if v else 'closed') + '\n'
                          for n, v in sorted(combined.items()))
    return wanted_text, {'inherited_results_unchanged': len(inherited),
                        'added_results': len(expected),
                        'added_closed': sum(not v for v in actual.values()),
                        'total_results': len(combined),
                        'exact_per_result_namespace_transport_dependencies': True}


def contracts(receipt, base, candidate):
    parser = load('scalar_contract_parser', ARCHIVE.parent / 'ge-negate/review-full-snapshots.py')
    results = [('C.' + e['name'], n) for e in receipt['modules'] for n in e['results']]
    definitions = [('C.' + e['name'], n) for e in receipt['modules'] for n in e['definitions']]
    old_results = parser.rows(base / 'C/jet_public_theorems.txt')
    old_definitions = parser.rows(base / 'C/jet_contract_definitions.txt', parser.LEGACY_DUPLICATE_DEFINITIONS)
    if (parser.rows(candidate / 'C/jet_public_theorems.txt') != old_results + results
            or parser.rows(candidate / 'C/jet_contract_definitions.txt', parser.LEGACY_DUPLICATE_DEFINITIONS)
               != old_definitions + definitions):
        raise ValueError('audit inventories are not exact append-only extensions')
    names, old_names = {n for _, n in results + definitions}, {n for _, n in old_results + old_definitions}
    if names & old_names or len(names) != len(results + definitions):
        raise ValueError('unexpected printed name collision')
    chunks = parser.chunks((candidate / 'C/jet_contracts.expected').read_text(), names | old_names,
                           inherited_print_context=True)
    if ''.join(t for n, t in chunks if n not in names) != (base / 'C/jet_contracts.expected').read_text():
        raise ValueError('inherited contract bytes changed')
    added = [(n, t) for n, t in chunks if n in names]
    if [n for n, _ in added] != [n for _, n in results + definitions]:
        raise ValueError('new contract records missing/reordered/duplicated')
    work = candidate.parent
    deep = (work / 'deep-full-contracts.out').read_text()
    if (work / 'deep-full-contracts.err').read_bytes() or '...' in deep:
        raise ValueError('deep report truncated or contains diagnostics')
    markers = list(re.finditer(r'(?m)^SCALAR_(TYPE|DEF) (\S+)\n', deep))
    wanted = [('TYPE', mod + '.' + n) for mod, n in results]
    wanted += [('DEF', mod + '.' + n) for mod, n in definitions if not n.endswith('_tree')]
    if [(m[1], m[2]) for m in markers] != wanted:
        raise ValueError('deep inventory drift')
    expanded = {(m[1], m[2]): deep[m.end():markers[i + 1].start() if i + 1 < len(markers) else len(deep)]
                for i, m in enumerate(markers)}
    compact = lambda s: re.sub(r'\s+', '', s)
    supplements, trees = [], []
    for i, ((mod, name), (_, text)) in enumerate(zip(results + definitions, added)):
        kind, key = ('TYPE' if i < len(results) else 'DEF'), mod + '.' + name
        if kind == 'DEF' and name.endswith('_tree'):
            trees.append(key)
            continue
        current, full = compact(text), compact(expanded[(kind, key)])
        if current == full:
            continue
        position = 0
        fragments = current.split('...')
        for j, fragment in enumerate(fragments):
            offset = (len(full) - len(fragment) if j == len(fragments) - 1 and full.endswith(fragment)
                      else full.find(fragment, position))
            if offset < position or (j == 0 and offset != 0):
                raise ValueError('non-print-depth difference: ' + key)
            position = offset + len(fragment)
        if '...' not in current or position != len(full):
            raise ValueError('unexpected contract difference: ' + key)
        supplements.append(key)
    return {'inherited_contracts_byte_identical': True, 'new_types': len(results),
            'new_definitions': len(definitions), 'all_non_tree_terms_untruncated': True,
            'deep_ellipsis_supplements': supplements, 'execution_tree_prints_diagnostic_only': trees,
            'source_and_execution_shape_proofs_required': True}


def review(prepare=False):
    receipt, base, candidate = inputs()
    wanted_text, assumptions = dependencies(receipt, base, candidate)
    contract = contracts(receipt, base, candidate)
    path = candidate / 'C/jet_assumptions.expected'
    if prepare:
        if path.read_bytes() != (base / 'C/jet_assumptions.expected').read_bytes():
            raise ValueError('assumption snapshot already prepared/changed')
        diff = list(difflib.unified_diff(path.read_text().splitlines(), wanted_text.splitlines(), n=3))[2:]
        patch = ['*** Begin Patch', '*** Update File: ' + str(path)]
        patch += ['@@' if line.startswith('@@') else line for line in diff]
        patch.append('*** End Patch')
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    if path.read_text() != wanted_text:
        raise ValueError('normal assumption snapshot is not exact reviewed extension')
    outputs = ['normal-build.log', 'normal-contract-generation.log', 'new-assumptions.out',
               'new-assumptions.err', 'deep-full-contracts.out', 'deep-full-contracts.err',
               'scalar_integration_assumptions.v', 'scalar_integration_deep_full_context.v']
    result = {'candidate': receipt['candidate'], 'parent_full_acceptance_session': 45608,
            **assumptions, **contract,
            'snapshot_hashes': {n: sha(candidate / 'C' / n) for n in
                               ['jet_assumptions.expected', 'jet_contracts.expected', 'jet_coqchk_axioms.expected']},
            'output_hashes': {n: sha(candidate.parent / n) for n in outputs},
            'all_sources_and_infrastructure_unchanged': True,
            'full_acceptance': False, 'checkout_coverage_added': 0}
    pinned_path = ARCHIVE / 'NORMAL-REVIEW.json'
    if pinned_path.exists():
        pinned = json.loads(pinned_path.read_text())
        if any(pinned.get(key) != value for key, value in result.items()):
            raise ValueError('reviewed normal evidence receipt changed')
    return result


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--prepare-assumptions', action='store_true')
    args = cli.parse_args()
    print(json.dumps(review(args.prepare_assumptions), indent=2))
