"""Exact normal square source/type/dependency review; never full acceptance.

The explicit preparation mode installs only the reconciled assumption extension.
It does not accept generated type/definition snapshots or run a proof gate.
"""
import argparse
import difflib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


parent = load('square_ordered_contracts', ARCHIVE.parent / 'scalar-multiply-integration/review-normal.py')
contract_records, assumptions = parent.contract_records, parent.assumptions


def dependencies(assembly, candidate):
    original = {}
    for directory, report in [('/tmp/jet-scalar-square.xWr06l', 'square_assumptions.out'),
                              ('/tmp/jet-scalar-square-function.FMkNQs', 'square_function_assumptions.out'),
                              ('/tmp/jet-scalar-square-literal.aDYc46', 'square_public_assumptions.out')]:
        for name, deps in assumptions((Path(directory) / report).read_text()).items():
            if name in original:
                raise ValueError('duplicate original dependency record')
            original[name] = deps
    wanted = {'C.' + entry['name'] + '.' + name: original[entry['original_module'] + '.' + name]
              for entry in assembly['modules'] for name in entry['results']}
    actual = assumptions((candidate.parent / 'normal_assumptions.out').read_text())
    if actual != wanted or (candidate.parent / 'normal_assumptions.err').read_bytes():
        raise ValueError('new normal dependencies differ from checked counterparts')
    return actual


def contracts(assembly, base, candidate):
    r0, d0 = parent.rows(base / 'C/jet_public_theorems.txt'), parent.rows(base / 'C/jet_contract_definitions.txt')
    r1, d1 = parent.rows(candidate / 'C/jet_public_theorems.txt'), parent.rows(candidate / 'C/jet_contract_definitions.txt')
    added_r = [('C.' + entry['name'], name) for entry in assembly['modules'] for name in entry['results']]
    added_d = [('C.' + entry['name'], name) for entry in assembly['modules'] for name in entry['definitions']]
    if r1 != r0 + added_r or d1 != d0 + added_d:
        raise ValueError('inventories not exact ordered extensions')
    old = contract_records((base / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = contract_records((candidate / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {key for key, _ in old}
    if [(key, text) for key, text in new if key in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(key, text) for key, text in new if key not in old_keys]
    report = (candidate.parent / 'normal_deep_contracts.out').read_text()
    markers = list(re.finditer(r'(?m)^NORMAL_SQUARE_(TYPE|DEF) (\S+)\n', report))
    expected = [('TYPE', mod + '.' + name) for mod, name in added_r] + [('DEF', mod + '.' + name) for mod, name in added_d]
    if ('...' in report or (candidate.parent / 'normal_deep_contracts.err').read_bytes()
            or [(m[1], m[2]) for m in markers] != expected):
        raise ValueError('deep contract report incomplete/truncated')
    expanded = {(m[1], m[2]): report[m.end():markers[i + 1].start() if i + 1 < len(markers) else len(report)]
                for i, m in enumerate(markers)}
    supplements = []
    for (kind, mod, name, _), text in added:
        short, full = re.sub(r'\s+', '', text), re.sub(r'\s+', '', expanded[(kind, mod + '.' + name)])
        if short == full:
            continue
        position = 0; fragments = short.split('...')
        for i, fragment in enumerate(fragments):
            offset = (len(full) - len(fragment) if i == len(fragments) - 1 and full.endswith(fragment)
                      else full.find(fragment, position))
            if offset < position or i == 0 and offset != 0:
                raise ValueError('non-print-depth contract difference')
            position = offset + len(fragment)
        if '...' not in short or position != len(full):
            raise ValueError('unexplained compact/deep contract difference')
        supplements.append(mod + '.' + name)
    return {'inherited_contract_records': len(old), 'inherited_contract_bytes_identical': True,
            'new_types': len(added_r), 'new_definitions': len(added_d),
            'deep_report_bytes': len(report.encode()), 'deep_ellipsis_supplements': supplements}


def review(assembly_path, prepare=False):
    assembly = json.loads(assembly_path.read_text())
    base, candidate = Path(assembly['baseline']) / 'Coq', Path(assembly['candidate']) / 'Coq'
    assembler = load('square_normal_assembler', ARCHIVE / 'assemble-candidate.py')
    if assembler.assemble(base.parent, candidate.parent, verify=True) != assembly:
        raise ValueError('assembly/provenance/source drift')
    # All inherited audit inputs stay byte-identical, except the exact planned
    # registry/gate extensions and the separately reviewed snapshot extensions.
    exceptions = set(assembly['metadata']) | {'C/jet_contracts.expected', 'C/jet_assumptions.expected'}
    for path in base.rglob('*'):
        if not path.is_file() or '__pycache__' in path.parts:
            continue
        rel = str(path.relative_to(base))
        if path.suffix not in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} and not path.name.startswith('_CoqProject'):
            continue
        if rel not in exceptions and path.read_bytes() != (candidate / rel).read_bytes():
            raise ValueError('inherited infrastructure changed: ' + rel)
    dependency = dependencies(assembly, candidate); contract = contracts(assembly, base, candidate)
    old = {}
    for line in (base / 'C/jet_assumptions.expected').read_text().splitlines():
        name, deps = line.split(' : ', 1); old[name] = set() if deps == 'closed' else set(deps.split(', '))
    if set(old) & set(dependency):
        raise ValueError('new/inherited dependency collision')
    combined = {**old, **dependency}
    wanted = ''.join(name + ' : ' + (', '.join(sorted(deps)) if deps else 'closed') + '\n'
                     for name, deps in sorted(combined.items()))
    path = candidate / 'C/jet_assumptions.expected'
    if prepare:
        if path.read_bytes() != (base / 'C/jet_assumptions.expected').read_bytes():
            raise ValueError('assumptions already prepared/changed')
        diff = list(difflib.unified_diff(path.read_text().splitlines(), wanted.splitlines(), n=3))[2:]
        patch = ['*** Begin Patch', '*** Update File: ' + str(path)]
        patch += ['@@' if line.startswith('@@') else line for line in diff]; patch.append('*** End Patch')
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True, stdout=subprocess.DEVNULL)
    if path.read_text() != wanted:
        raise ValueError('assumption snapshot not the exact reviewed extension')
    common = load('square_kernel_context', ARCHIVE.parent / 'scalar-mul/review.py')
    common.kernel((candidate.parent / 'normal-kernel.log').read_text(),
                  sorted((base / 'C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate': assembly['candidate'], 'baseline': assembly['baseline'], **contract,
            'inherited_assumption_records': len(old), 'new_assumption_records': len(dependency),
            'new_closed_results': sum(not deps for deps in dependency.values()),
            'normal_kernel_context_matches': True, 'exact_namespace_dependencies': True,
            'inherited_infrastructure_unchanged': True,
            'snapshot_hashes': {name: parent.sha(candidate / 'C' / name) for name in
                               ['jet_contracts.expected', 'jet_assumptions.expected', 'jet_coqchk_axioms.expected']},
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--assembly', type=Path, required=True)
    cli.add_argument('--prepare-assumptions', action='store_true'); args = cli.parse_args()
    print(json.dumps(review(args.assembly, args.prepare_assumptions), indent=2))
