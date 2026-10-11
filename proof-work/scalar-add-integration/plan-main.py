"""Read-only main reconciliation plan. Never installs sources or accepts proofs."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
from collections import Counter
import subprocess
import sys
sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
repo = archive.parent.parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def lines(path):
    return [line.strip() for line in path.read_text().splitlines()
            if line.strip() and not line.startswith('#')]


def contract_records(text, results, definitions):
    """Split the standard Check/Print output without losing duplicate names.

    The inventory fixes command order. A mutual fixpoint's trailing `for f`
    is part of its Print, not a second command. Variant/Record declarations
    may put the name and parameters on the next line.
    """
    inventory = [('TYPE', mod, name) for mod, name in results]
    inventory += [('DEF', mod, name) for mod, name in definitions]
    names = '|'.join(map(re.escape, sorted({n.split('.')[-1] for _, _, n in inventory},
                                         key=len, reverse=True)))
    identifier = r"@?(?:[A-Za-z_][\w']*\.)*(?:" + names + ')'
    pattern = (r'(?m)^(?:(?:Variant|Record|Inductive)\s+(?P<decl>' + identifier + r')\b'
               r'|(?P<value>' + identifier + r')(?=(?:[ \t]*[:=]|(?:[ \t]+\?[\w]+)*\n[ \t]+:)))')
    matches = [m for m in re.finditer(pattern, text)
               if text[max(0, m.start() - 4):m.start()] != 'for\n']
    if not matches or matches[0].start() != 0 or len(matches) != len(inventory):
        raise ValueError('snapshot command count/prefix mismatch: '
                         + str((len(matches), len(inventory))))
    occurrences = Counter()
    records = []
    for i, (match, row) in enumerate(zip(matches, inventory)):
        kind, mod, name = row
        label = (match['decl'] or match['value']).lstrip('@')
        full = mod + '.' + name
        if full != label and not full.endswith('.' + label):
            raise ValueError('snapshot declaration/order mismatch: ' + str((i, row, label)))
        occurrences[row] += 1
        key = (*row, occurrences[row])
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        records.append((key, text[match.start():end]))
    return records


def compare_contracts(old_records, new_records):
    old_map = dict(old_records)
    inherited = [(key, text) for key, text in new_records if key in old_map]
    changed = [{'kind': k[0], 'module': k[1], 'name': k[2], 'occurrence': k[3],
                'main_sha256': sha(old_map[k].encode()),
                'candidate_sha256': sha(t.encode())}
               for k, t in inherited if t != old_map[k]]
    return {
        'inherited_contract_bytes_identical': inherited == old_records,
        'changed_contract_records': changed,
        'missing_contract_records': [k for k, _ in old_records if k not in dict(inherited)],
        'inherited_contract_order_preserved': [k for k, _ in inherited] == [k for k, _ in old_records],
        'inherited_contract_records': len(old_records),
        'new_contract_records': len(new_records) - len(inherited),
    }


def plan(candidate):
    candidate = candidate.resolve()
    main = repo / 'Coq'
    sources, same, conflicts = [], [], []
    for path in sorted(candidate.rglob('*.v')):
        rel = path.relative_to(candidate)
        target = main / rel
        data = path.read_bytes()
        if not target.exists():
            sources.append({'path': str(rel), 'sha256': sha(data)})
        elif target.read_bytes() == data:
            same.append(str(rel))
        else:
            conflicts.append({'path': str(rel), 'main_sha256': sha(target.read_bytes()),
                              'candidate_sha256': sha(data)})
    main_only = sorted(str(p.relative_to(main)) for p in main.rglob('*.v')
                       if not (candidate / p.relative_to(main)).exists())
    extensions = {}
    for name in ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
                 'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv']:
        old, new = lines(main / name), lines(candidate / name)
        common = [r for r in new if r in set(old)]
        missing = [r for r in old if r not in set(new)]
        extensions[name] = {
            'main_sha256': sha((main / name).read_bytes()),
            'candidate_sha256': sha((candidate / name).read_bytes()),
            'main_rows': len(old), 'candidate_rows': len(new),
            'main_rows_preserved_in_order': common == old,
            'main_rows_missing': missing,
            'candidate_additions': [r for r in new if r not in set(old)],
            'main_is_byte_prefix': (candidate / name).read_bytes().startswith((main / name).read_bytes())}
    parser = load('main_reconciliation_snapshots', archive.parent / 'ge-negate/review-full-snapshots.py')
    old_deps = parser.assumptions(main / 'C/jet_assumptions.expected')
    new_deps = parser.assumptions(candidate / 'C/jet_assumptions.expected')
    changed_deps = {n: {'main': v, 'candidate': new_deps.get(n)}
                    for n, v in old_deps.items() if new_deps.get(n) != v}
    old_results = parser.rows(main / 'C/jet_public_theorems.txt')
    old_defs = parser.rows(main / 'C/jet_contract_definitions.txt', parser.LEGACY_DUPLICATE_DEFINITIONS)
    new_results = parser.rows(candidate / 'C/jet_public_theorems.txt')
    new_defs = parser.rows(candidate / 'C/jet_contract_definitions.txt', parser.LEGACY_DUPLICATE_DEFINITIONS)
    old_text = (main / 'C/jet_contracts.expected').read_text()
    old_records = contract_records(old_text, old_results, old_defs)
    new_records = contract_records((candidate / 'C/jet_contracts.expected').read_text(),
                                   new_results, new_defs)
    contract_comparison = compare_contracts(old_records, new_records)
    # Git index remains untouched. Record staged and worktree versions of
    # scoped metadata independently, so a later application cannot confuse them.
    index = {}
    for name in extensions:
        result = subprocess.run(['git', 'show', ':' + 'Coq/' + name], cwd=repo,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
        index[name] = sha(result.stdout)
    acceptance_path = archive / 'ACCEPTANCE.json'
    accepted = False
    if acceptance_path.exists():
        receipt = json.loads(acceptance_path.read_text())
        accepted = (Path(receipt['candidate']).resolve() / 'Coq' == candidate
                    and receipt['exit_code'] == 0
                    and sha(Path(receipt['log']).read_bytes()) == receipt['log_sha256'])
    return {
        'candidate': str(candidate), 'main_checkout': str(main),
        'candidate_full_acceptance_receipt_present': accepted,
        'new_source_files': sources, 'same_source_count': len(same),
        'source_conflicts': conflicts, 'main_only_sources_preserved': main_only,
        'inventory_extensions': extensions, 'index_metadata_sha256': index,
        'inherited_assumption_records': len(old_deps),
        'candidate_assumption_records': len(new_deps),
        'changed_existing_dependencies': changed_deps,
        **contract_comparison,
        'kernel_allowlist_identical': (main / 'C/jet_coqchk_axioms.expected').read_bytes()
                                     == (candidate / 'C/jet_coqchk_axioms.expected').read_bytes(),
        'writes_performed': False, 'checkout_coverage_added': 0,
        'next': 'Resolve every conflict/missing row and inspect gate/coverage-tool extensions; application still requires full candidate acceptance and separate main verification.'}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--candidate-coq', type=Path, required=True)
    cli.add_argument('--summary', action='store_true')
    args = cli.parse_args()
    result = plan(args.candidate_coq)
    if args.summary:
        result = {**{k: v for k, v in result.items()
                     if k not in {'new_source_files', 'inventory_extensions', 'index_metadata_sha256'}},
                  'new_source_count': len(result['new_source_files']),
                  'inventories': {n: {k: v for k, v in e.items()
                                     if k not in {'candidate_additions', 'main_sha256', 'candidate_sha256'}}
                                  | {'candidate_addition_count': len(e['candidate_additions'])}
                                  for n, e in result['inventory_extensions'].items()}}
    print(json.dumps(result, indent=2))
