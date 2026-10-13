"""Review the exact registry/snapshot delta; optional worktree-only install.

The isolated candidate prepares snapshots. Acceptance is then run on the
actual main worktree, without update flags. Installation never alters staging
or proof sources and is not, by itself, a claim of acceptance.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


assembly = load(HERE / 'assemble.py', 'nullable_assembly_tools')
normal = load(HERE.parent / 'scalar-multiply-integration/review-normal.py', 'nullable_contract_records')


def dependencies(text):
    records = {}
    for line in text.splitlines():
        name, deps = line.split(' : ', 1)
        if name in records:
            raise ValueError('duplicate dependency record')
        records[name] = [] if deps == 'closed' else deps.split(', ')
    return records


def review(candidate):
    candidate = candidate.resolve()
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    coq = candidate / 'Coq'
    if candidate != Path(meta['candidate']).resolve():
        raise ValueError('candidate identity mismatch')
    for name, value in meta['main_metadata_sha256'].items():
        if assembly.sha((assembly.MAIN / name).read_bytes()) != value:
            raise ValueError('main metadata changed; reassemble rather than overwrite: ' + name)
    for name, value in meta['main_index_sha256'].items():
        if assembly.sha(subprocess.check_output(['git', 'show', ':Coq/' + name], cwd=REPO)) != value:
            raise ValueError('existing staging changed')
    if assembly.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != meta['main_staged_patch_sha256']:
        raise ValueError('staged patch changed')
    exceptions = set(assembly.FILES)
    for path in assembly.MAIN.rglob('*'):
        if not path.is_file() or '__pycache__' in path.parts:
            continue
        rel = str(path.relative_to(assembly.MAIN))
        if rel not in exceptions and (path.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}
                                     or path.name.startswith('_CoqProject')):
            if path.read_bytes() != (coq / rel).read_bytes():
                raise ValueError('inherited source/infrastructure drift: ' + rel)
    for name, added in meta['extensions'].items():
        if (coq / name).read_text() != (assembly.MAIN / name).read_text() + '\n'.join(added) + '\n':
            raise ValueError('inventory change is not the exact ordered extension')
    old_coverage = (assembly.MAIN / 'C/jet_coverage.tsv').read_text()
    matches = [line for line in old_coverage.splitlines() if ' '.join(line.split()) == meta['old_coverage_row']]
    if len(matches) != 1 or (coq / 'C/jet_coverage.tsv').read_text() != old_coverage.replace(matches[0], meta['new_coverage_row'], 1):
        raise ValueError('coverage changes more than the existing tappath row')
    r0 = normal.rows(assembly.MAIN / 'C/jet_public_theorems.txt')
    d0 = normal.rows(assembly.MAIN / 'C/jet_contract_definitions.txt')
    r1 = normal.rows(coq / 'C/jet_public_theorems.txt')
    d1 = normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((assembly.MAIN / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {key for key, _ in old}
    if [(key, text) for key, text in new if key in old_keys] != old:
        raise ValueError('an inherited contract changed bytes or order')
    added = [(key, text) for key, text in new if key not in old_keys]
    if len(added) != 10:
        raise ValueError('unexpected nullable contract extension')
    # The ordinary gate uses Coq's compact printer. Independently retain and
    # inspect the fully expanded new records, matching every printed fragment.
    import re
    report = (candidate / 'new_contracts.out').read_text()
    marks = list(re.finditer(r'(?m)^NULLABLE_DEEP_(TYPE|DEF) (\S+)\n', report))
    wanted = [(kind, mod + '.' + name) for (kind, mod, name, _), _ in added]
    if [(m[1], m[2]) for m in marks] != wanted:
        raise ValueError('deep nullable records missing/reordered')
    supplements = []
    for i, ((kind, mod, name, _), text) in enumerate(added):
        full = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in full:
            raise ValueError('deep nullable record truncated')
        short, long = re.sub(r'\s+', '', text), re.sub(r'\s+', '', full)
        if short == long:
            continue
        position = 0
        fragments = short.split('...')
        for j, fragment in enumerate(fragments):
            offset = (len(long) - len(fragment) if j == len(fragments)-1 and long.endswith(fragment)
                      else long.find(fragment, position))
            if offset < position or j == 0 and offset != 0:
                raise ValueError('compact/full nullable type disagreement')
            position = offset + len(fragment)
        if '...' not in short or position != len(long):
            raise ValueError('unexplained compact/full nullable type difference')
        supplements.append(mod + '.' + name)
    dep0 = dependencies((assembly.MAIN / 'C/jet_assumptions.expected').read_text())
    dep1 = dependencies((coq / 'C/jet_assumptions.expected').read_text())
    if {name: dep1.get(name) for name in dep0} != dep0:
        raise ValueError('inherited theorem dependencies changed')
    receipt = json.loads((HERE.parent / 'shared-foundations-integration/REVIEW.json').read_text())
    added_names = [module + '.' + name for module, name in r1[len(r0):]]
    added_deps = {name: deps for name, deps in dep1.items() if name not in dep0}
    if added_deps != {name: receipt['assumptions'][name] for name in added_names}:
        raise ValueError('new theorem dependencies differ from independent checks')
    for name, value in meta['source_sha256'].items():
        if assembly.sha((REPO / name).read_bytes()) != value:
            raise ValueError('checked nullable source changed')
    for module, theorem in r1[len(r0):]:
        if not (coq / (module.replace('.', '/') + '.vo')).is_file():
            raise ValueError('nullable module not explicitly compiled')
    return {'candidate': str(candidate), 'inherited_contract_records': len(old),
            'inherited_contract_bytes_and_order_identical': True,
            'inherited_assumption_records': len(dep0), 'inherited_dependencies_unchanged': True,
            'new_results': len(added_names), 'new_definitions': len(d1) - len(d0),
            'deep_print_supplements': supplements,
            'exact_prechecked_new_dependencies': True, 'coverage_added': 0,
            'snapshots_sha256': {name: assembly.sha((coq / name).read_bytes()) for name in assembly.FILES},
            'main_staged_patch_sha256': meta['main_staged_patch_sha256'],
            'full_acceptance': False, 'main_installation': False}


def install(candidate):
    result = review(candidate)
    sources = {str(path.relative_to(assembly.MAIN)): assembly.sha(path.read_bytes())
               for path in assembly.MAIN.rglob('*.v')}
    content = {assembly.MAIN / name: (candidate / 'Coq' / name).read_text() for name in assembly.FILES}
    assembly.patch_files(content)
    for path, text in content.items():
        if path.read_text() != text:
            raise ValueError('installed metadata mismatch')
    for name, value in sources.items():
        if assembly.sha((assembly.MAIN / name).read_bytes()) != value:
            raise ValueError('existing proof changed during install')
    if assembly.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != result['main_staged_patch_sha256']:
        raise ValueError('existing staging changed during install')
    result['main_installation'] = True
    result['next'] = 'Freeze actual main inputs; run check-jets.sh --accept without update/no-build flags.'
    return result


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    cli.add_argument('--apply', action='store_true'); args = cli.parse_args()
    print(json.dumps(install(args.candidate) if args.apply else review(args.candidate), indent=2))
