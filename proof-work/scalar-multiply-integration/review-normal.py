"""Exact normal source/contract/dependency reconciliation, not acceptance.

Optional preparation installs only the exactly reconciled assumption snapshot.
The later full --accept gate must rebuild/check/compare it without update flags.
"""
import argparse
from collections import Counter
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
REPO = ARCHIVE.parent.parent
CONSTRUCTOR_PRINTS = {
    ('C.jet_secp_reduce512_wide', 'wcolumn'): 'wide_column',
    ('C.jet_secp_reduce512_accumulate', 'Wmul'): 'wide_operation',
    ('C.jet_secp_reduce512_accumulate', 'Wsum'): 'wide_operation',
}
INHERITED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep',
             'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
             'Events.external_functions_sem', 'Events.external_functions_properties',
             'Events.inline_assembly_sem', 'Events.inline_assembly_properties'}


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rows(path):
    return [tuple(line.split()) for line in path.read_text().splitlines()
            if line.strip() and not line.startswith('#')]


def contract_records(text, results, definitions):
    inventory = [('TYPE', mod, name) for mod, name in results]
    inventory += [('DEF', mod, name) for mod, name in definitions]
    print_names = {n.split('.')[-1] for _, _, n in inventory}
    print_names.update(CONSTRUCTOR_PRINTS[(mod, name)] for kind, mod, name in inventory
                       if kind == 'DEF' and (mod, name) in CONSTRUCTOR_PRINTS)
    names = '|'.join(map(re.escape, sorted(print_names, key=len, reverse=True)))
    identifier = r"@?(?:[A-Za-z_][\w']*\.)*(?:" + names + ')'
    pattern = (r'(?m)^(?:(?:Variant|Record|Inductive)\s+(?P<decl>' + identifier + r')\b'
               r'|(?P<value>' + identifier + r')(?=(?:[ \t]*[:=]|(?:[ \t]+\?[\w]+)*\n[ \t]+:)))')
    matches = [m for m in re.finditer(pattern, text)
               if text[max(0, m.start() - 4):m.start()] != 'for\n']
    if not matches or matches[0].start() != 0 or len(matches) != len(inventory):
        raise ValueError('snapshot command count/prefix mismatch')
    occurrences, records = Counter(), []
    for i, (match, row) in enumerate(zip(matches, inventory)):
        kind, mod, name = row
        label = (match['decl'] or match['value']).lstrip('@')
        full = mod + '.' + name
        parent = CONSTRUCTOR_PRINTS.get((mod, name)) if kind == 'DEF' else None
        alias = parent and label in {parent, mod + '.' + parent, mod.removeprefix('C.') + '.' + parent}
        if not alias and full != label and not full.endswith('.' + label):
            raise ValueError('snapshot declaration/order mismatch: ' + str((i, row, label)))
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        chunk = text[match.start():end]
        if alias and not re.search(r'\b' + re.escape(name) + r'\s*:', chunk):
            raise ValueError('constructor missing from its repeated parent Print')
        occurrences[row] += 1
        records.append(((*row, occurrences[row]), chunk))
    return records


def assumptions(text):
    text = text.replace('PRODUCT_ASSUMPTIONS ', 'JET_ASSUMPTIONS ')
    result, current, mode = {}, None, None
    def finish():
        if current is not None and (mode is None or mode == 'axioms' and not result[current]):
            raise ValueError('unfinished/empty assumption report: ' + current)
    for line in text.splitlines():
        match = re.fullmatch(r'JET_ASSUMPTIONS (\S+)', line)
        if match:
            finish(); current = match[1]
            if current in result:
                raise ValueError('duplicate assumption marker')
            result[current], mode = set(), None
        elif line == 'Axioms:':
            if current is None or mode is not None:
                raise ValueError('unexpected axiom section')
            mode = 'axioms'
        elif line.startswith('Closed under the global context'):
            if current is None or mode is not None:
                raise ValueError('unexpected closed section')
            mode = 'closed'
        elif mode == 'axioms' and line and not line[0].isspace():
            result[current].add(line.split()[0])
    finish()
    if set().union(set(), *result.values()) - INHERITED:
        raise ValueError('unexpected non-inherited dependency')
    return result


def dependencies(assembly, candidate):
    original = {}
    workdirs = ['/tmp/jet-scalar-mul.lkomWj', '/tmp/jet-scalar-mul-boundary.TchFPw',
                '/tmp/jet-scalar-mul-public.nzHcef', '/tmp/jet-scalar-mul-ownership.Ste5AV']
    for directory in workdirs:
        for path in sorted(Path(directory).glob('*assumptions.out')):
            for name, deps in assumptions(path.read_text()).items():
                if name in original and original[name] != deps:
                    raise ValueError('historical dependency disagreement')
                original[name] = deps
    expected = {'C.' + entry['name'] + '.' + name: original[entry['original_module'] + '.' + name]
                for entry in assembly['modules'] for name in entry['results']}
    actual = assumptions((candidate.parent / 'new-assumptions.out').read_text())
    if actual != expected or (candidate.parent / 'new-assumptions.err').read_bytes():
        raise ValueError('normal dependencies differ from the checked namespace closure')
    return actual


def contracts(assembly, base, candidate):
    r0, d0 = rows(base / 'C/jet_public_theorems.txt'), rows(base / 'C/jet_contract_definitions.txt')
    r1, d1 = rows(candidate / 'C/jet_public_theorems.txt'), rows(candidate / 'C/jet_contract_definitions.txt')
    added_results = [('C.' + entry['name'], name) for entry in assembly['modules'] for name in entry['results']]
    added_defs = [('C.' + entry['name'], name) for entry in assembly['modules'] for name in entry['definitions']]
    if r1 != r0 + added_results or d1 != d0 + added_defs:
        raise ValueError('inventories not exact append-only extensions')
    old = contract_records((base / 'C/jet_contracts.expected').read_text(), r0, d0)
    all_records = contract_records((candidate / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {key for key, _ in old}
    inherited = [(key, text) for key, text in all_records if key in old_keys]
    if inherited != old:
        raise ValueError('inherited contract bytes or order changed')
    added = [(key, text) for key, text in all_records if key not in old_keys]
    report = (candidate.parent / 'deep-contracts.out').read_text()
    markers = list(re.finditer(r'(?m)^NORMAL_MULTIPLY_(TYPE|DEF) (\S+)\n', report))
    wanted = [('TYPE', mod + '.' + name) for mod, name in added_results]
    wanted += [('DEF', mod + '.' + name) for mod, name in added_defs if not name.endswith('_tree')]
    if ('...' in report or (candidate.parent / 'deep-contracts.err').read_bytes()
            or [(m[1], m[2]) for m in markers] != wanted):
        raise ValueError('deep inventory/report incomplete')
    expanded = {(m[1], m[2]): report[m.end():markers[i + 1].start() if i + 1 < len(markers) else len(report)]
                for i, m in enumerate(markers)}
    supplements, trees = [], []
    for (kind, mod, name, occurrence), text in added:
        key = (kind, mod + '.' + name)
        if kind == 'DEF' and name.endswith('_tree'):
            trees.append(key[1]); continue
        short, full = re.sub(r'\s+', '', text), re.sub(r'\s+', '', expanded[key])
        if short == full:
            continue
        position = 0
        fragments = short.split('...')
        for j, fragment in enumerate(fragments):
            offset = (len(full) - len(fragment) if j == len(fragments) - 1 and full.endswith(fragment)
                      else full.find(fragment, position))
            if offset < position or j == 0 and offset != 0:
                raise ValueError('non-print-depth contract difference: ' + str(key))
            position = offset + len(fragment)
        if '...' not in short or position != len(full):
            raise ValueError('unexplained contract difference: ' + str(key))
        supplements.append(key[1])
    return {'inherited_contract_records': len(old), 'inherited_contract_bytes_identical': True,
            'new_types': len(added_results), 'new_definitions': len(added_defs),
            'untruncated_non_tree_report_bytes': len(report.encode()),
            'deep_ellipsis_supplements': supplements, 'diagnostic_execution_trees': trees,
            'constructor_parent_print_aliases': list(CONSTRUCTOR_PRINTS)}


def review(assembly_path, prepare=False):
    assembly = json.loads(assembly_path.read_text())
    base, candidate = Path(assembly['baseline']) / 'Coq', Path(assembly['candidate']) / 'Coq'
    assembler = load('multiply_normal_assembler', ARCHIVE / 'assemble-candidate.py')
    verified = assembler.assemble(base.parent, candidate.parent, verify=True)
    if verified != assembly:
        raise ValueError('assembly/source/provenance drift')
    dependency = dependencies(assembly, candidate)
    contract = contracts(assembly, base, candidate)
    parent = {}
    for line in (base / 'C/jet_assumptions.expected').read_text().splitlines():
        name, deps = line.split(' : ', 1)
        parent[name] = set() if deps == 'closed' else set(deps.split(', '))
    if set(parent) & set(dependency):
        raise ValueError('new/inherited dependency collision')
    combined = {**parent, **dependency}
    wanted = ''.join(name + ' : ' + (', '.join(sorted(deps)) if deps else 'closed') + '\n'
                     for name, deps in sorted(combined.items()))
    path = candidate / 'C/jet_assumptions.expected'
    if prepare:
        if path.read_bytes() != (base / 'C/jet_assumptions.expected').read_bytes():
            raise ValueError('assumptions already prepared or changed')
        diff = list(difflib.unified_diff(path.read_text().splitlines(), wanted.splitlines(), n=3))[2:]
        patch = ['*** Begin Patch', '*** Update File: ' + str(path)]
        patch += ['@@' if line.startswith('@@') else line for line in diff]
        patch.append('*** End Patch')
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    if path.read_text() != wanted:
        raise ValueError('assumption snapshot is not the exact reviewed extension')
    if (candidate / 'C/jet_coqchk_axioms.expected').read_bytes() != (base / 'C/jet_coqchk_axioms.expected').read_bytes():
        raise ValueError('kernel context allowlist changed')
    common = load('multiply_normal_kernel', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((candidate.parent / 'normal-kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    for name in ['normal-build.log', 'normal-contract-generation.log']:
        if not (candidate.parent / name).exists():
            raise ValueError('missing terminal-run evidence log')
    return {'candidate': assembly['candidate'], 'baseline': assembly['baseline'],
            **contract, 'inherited_assumption_records': len(parent),
            'new_assumption_records': len(dependency), 'new_closed_results': sum(not ds for ds in dependency.values()),
            'exact_per_result_namespace_dependencies': True, 'normal_kernel_context_matches': True,
            'snapshot_hashes': {name: sha(candidate / 'C' / name) for name in
                               ['jet_assumptions.expected', 'jet_contracts.expected', 'jet_coqchk_axioms.expected']},
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--assembly', type=Path, required=True)
    cli.add_argument('--prepare-assumptions', action='store_true')
    args = cli.parse_args()
    print(json.dumps(review(args.assembly, args.prepare_assumptions), indent=2))
