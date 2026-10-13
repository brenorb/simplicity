"""Append-only Elements Version admission with independent snapshot review.

assemble/prepare/check write only a dedicated candidate. install changes main's
seven metadata files, never its existing staging. Full --accept remains a
separate mandatory terminal check; snapshot preparation is not acceptance.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
MAIN = REPO / 'Coq'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    return mod


patch = load('version_admission_patch', HERE.parent / 'nullable-admission/assemble.py')
normal = load('version_admission_records', HERE.parent / 'scalar-multiply-integration/review-normal.py')
nullable = load('version_dependency_records', HERE.parent / 'nullable-admission/review.py')
FILES = patch.FILES
COVERAGE = 'simplicity_version C.jet_elements_version_local elements_version_local_spec\n'
ENV = dict(os.environ, PATH='/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:' + os.environ['PATH'],
           PYTHONDONTWRITEBYTECODE='1')


def provenance():
    sourcing = json.loads((HERE.parent / 'elements-version-review/SOURCING.json').read_text())
    receipt = json.loads((HERE.parent / 'elements-version-review/REVIEW.json').read_text())
    for entry in sourcing['modules']:
        if patch.sha((MAIN / 'C' / entry['file']).read_bytes()) != entry['source_sha256']:
            raise ValueError('reviewed source changed: ' + entry['file'])
    for name, value in sourcing['inherited_dependency_hashes'].items():
        if patch.sha((MAIN / 'C' / (name + '.v')).read_bytes()) != value:
            raise ValueError('reviewed inherited dependency changed: ' + name)
    load('version_prior_evidence', HERE.parent / 'elements-version-review/review.py').review()
    return sourcing, receipt


def assemble():
    sourcing, receipt = provenance()
    candidate = Path(tempfile.mkdtemp(prefix='jet-elements-version-admission.', dir='/tmp')).resolve()
    coq = candidate / 'Coq'
    shutil.copytree(MAIN, coq, symlinks=True)
    for name in ['C', 'Haskell']:
        (candidate / name).symlink_to(REPO / name, target_is_directory=True)
    modules = [e['module'] for e in sourcing['modules']] + ['C.jet_application_contract']
    definitions = []
    for full in receipt['contracts']['definitions']:
        matches = [m for m in modules if full.startswith(m + '.')]
        if len(matches) != 1:
            raise ValueError('ambiguous definition module: ' + full)
        definitions.append((matches[0], full[len(matches[0]) + 1:]))
    old_defs = normal.rows(MAIN / 'C/jet_contract_definitions.txt')
    definitions = [(m, n) for m, n in definitions if (m, n) not in old_defs]
    extensions = {
        '_CoqProject': ['C/' + e['file'] for e in sourcing['modules']],
        '_CoqProject.jets': ['C/' + e['file'] for e in sourcing['modules']],
        'C/jet_public_theorems.txt': [e['module'] + ' ' + n for e in sourcing['modules'] for n in e['results']],
        'C/jet_contract_definitions.txt': [m + ' ' + n for m, n in definitions],
    }
    changes = {}
    for name, added in extensions.items():
        text = (MAIN / name).read_text()
        if not text.endswith('\n') or any(row in text.splitlines() for row in added):
            raise ValueError('non-fresh inventory extension')
        changes[coq / name] = text + '\n'.join(added) + '\n'
    old_coverage = (MAIN / 'C/jet_coverage.tsv').read_text()
    if any(line.split()[:1] == ['simplicity_version'] for line in old_coverage.splitlines()):
        raise ValueError('Version already registered')
    changes[coq / 'C/jet_coverage.tsv'] = old_coverage + COVERAGE
    meta = {'candidate': str(candidate), 'extensions': extensions,
            'main_metadata_sha256': {n: patch.sha((MAIN / n).read_bytes()) for n in FILES},
            'main_index_sha256': {n: patch.sha(subprocess.check_output(['git', 'show', ':Coq/' + n], cwd=REPO)) for n in FILES},
            'main_staged_patch_sha256': patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)),
            'source_sha256': {'Coq/C/' + e['file']: e['source_sha256'] for e in sourcing['modules']},
            'shared_commit': sourcing['shared_commit'], 'full_acceptance': False}
    changes[candidate / 'ASSEMBLY.json'] = json.dumps(meta, indent=2) + '\n'
    patch.patch_files(changes)
    print(json.dumps(meta, indent=2))


def run(candidate, command, stem, timeout=900):
    with (candidate / (stem + '.out')).open('wb') as out, (candidate / (stem + '.err')).open('wb') as err:
        done = subprocess.run(command, cwd=candidate / 'Coq', env=ENV, stdout=out, stderr=err, timeout=timeout)
    if done.returncode or (candidate / (stem + '.err')).read_bytes():
        raise ValueError('check failed; inspect ' + str(candidate / stem))


def prepare(candidate):
    sourcing, receipt = provenance()
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    coq = candidate / 'Coq'
    # Recompile every new module explicitly, avoiding stale copied objects.
    for e in sourcing['modules']:
        run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + e['file']], 'compile-' + Path(e['file']).stem)
    new_results = [tuple(row.split()) for row in meta['extensions']['C/jet_public_theorems.txt']]
    new_defs = [tuple(row.split()) for row in meta['extensions']['C/jet_contract_definitions.txt']]
    all_rows = normal.rows(coq / 'C/jet_public_theorems.txt') + normal.rows(coq / 'C/jet_contract_definitions.txt')
    driver = ['Set Warnings "-notation-overridden".']
    for module in sorted({m for m, _ in all_rows}):
        keyword = ('Require' if module.startswith(('Simplicity.', 'C.jet_elements_'))
                   or module == 'C.jet_secp_umul128_exec' else 'Require Import')
        driver.append(keyword + ' ' + module + '.')
    driver += ['Import Simplicity.BitMachine Simplicity.Translate.', 'Set Printing All.', 'Set Printing Width 120.']
    wanted = [('TYPE', m + '.' + n) for m, n in new_results] + [('DEF', m + '.' + n) for m, n in new_defs]
    for depth, marker in [(50, 'VERSION_COMPACT_'), (1000000, 'VERSION_DEEP_')]:
        driver.append('Set Printing Depth ' + str(depth) + '.')
        for kind, full in wanted:
            driver += ['Goal True. idtac "' + marker + kind + ' ' + full + '". exact I. Qed.',
                       ('Check ' if kind == 'TYPE' else 'Print ') + full + '.']
    patch.patch_files({candidate / 'new_contracts.v': '\n'.join(driver) + '\n'})
    run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', str(candidate / 'new_contracts.v')], 'new_contracts')
    report = (candidate / 'new_contracts.out').read_text().split('VERSION_DEEP_', 1)[0]
    marks = list(re.finditer(r'(?m)^VERSION_COMPACT_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != wanted or report[:marks[0].start()]:
        raise ValueError('new compact inventory missing/reordered')
    bodies = {wanted[i]: ''.join(line.rstrip() + '\n' for line in report[m.end():marks[i+1].start() if i+1 < len(marks) else len(report)].splitlines())
              for i, m in enumerate(marks)}
    old_records = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(),
                                          normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt'))
    contracts = ''.join(body for (k, _, _, _), body in old_records if k == 'TYPE')
    contracts += ''.join(bodies[('TYPE', m + '.' + n)] for m, n in new_results)
    contracts += ''.join(body for (k, _, _, _), body in old_records if k == 'DEF')
    contracts += ''.join(bodies[('DEF', m + '.' + n)] for m, n in new_defs)
    assumptions = nullable.dependencies((MAIN / 'C/jet_assumptions.expected').read_text())
    assumptions.update(receipt['expected_dependencies'])
    assumption_text = ''.join(name + ' : ' + (', '.join(deps) or 'closed') + '\n' for name, deps in sorted(assumptions.items()))
    patch.patch_files({coq / 'C/jet_contracts.expected': contracts, coq / 'C/jet_assumptions.expected': assumption_text})
    # These are actual fresh objects, not imported assumptions about execution.
    kernel(candidate)
    print(json.dumps(review(candidate), indent=2))


def kernel(candidate):
    provenance()
    # coqchk prints its successful context summary on stderr, unlike coqc.
    command = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', 'C.jet_elements_version_local']
    with (candidate / 'new_kernel.log').open('wb') as log:
        done = subprocess.run(command, cwd=candidate / 'Coq', env=ENV, stdout=log, stderr=subprocess.STDOUT, timeout=1800)
    patch.patch_files({candidate / 'KERNEL.json': json.dumps({'exit_code': done.returncode,
                      'log_sha256': patch.sha((candidate / 'new_kernel.log').read_bytes()), 'command': command}, indent=2) + '\n'})
    if done.returncode:
        raise ValueError('fresh closure kernel checker failed')


def review(candidate):
    sourcing, receipt = provenance()
    meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
    if Path(meta['candidate']).resolve() != candidate.resolve():
        raise ValueError('candidate identity drift')
    coq = candidate / 'Coq'
    for name, value in meta['main_metadata_sha256'].items():
        if patch.sha((MAIN / name).read_bytes()) != value:
            raise ValueError('main metadata changed; reassemble: ' + name)
    for name, value in meta['main_index_sha256'].items():
        if patch.sha(subprocess.check_output(['git', 'show', ':Coq/' + name], cwd=REPO)) != value:
            raise ValueError('original staging changed')
    if patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != meta['main_staged_patch_sha256']:
        raise ValueError('staged patch changed')
    for path in MAIN.rglob('*'):
        rel = str(path.relative_to(MAIN))
        if path.is_file() and '__pycache__' not in path.parts and rel not in FILES and (
                path.suffix in {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'} or path.name.startswith('_CoqProject')):
            if path.read_bytes() != (coq / rel).read_bytes():
                raise ValueError('candidate source/infrastructure drift: ' + rel)
    for name, added in meta['extensions'].items():
        if (coq / name).read_text() != (MAIN / name).read_text() + '\n'.join(added) + '\n':
            raise ValueError('inventory not exact append: ' + name)
    if (coq / 'C/jet_coverage.tsv').read_text() != (MAIN / 'C/jet_coverage.tsv').read_text() + COVERAGE:
        raise ValueError('coverage not exactly one Version addition')
    r0, d0 = normal.rows(MAIN / 'C/jet_public_theorems.txt'), normal.rows(MAIN / 'C/jet_contract_definitions.txt')
    r1, d1 = normal.rows(coq / 'C/jet_public_theorems.txt'), normal.rows(coq / 'C/jet_contract_definitions.txt')
    old = normal.contract_records((MAIN / 'C/jet_contracts.expected').read_text(), r0, d0)
    new = normal.contract_records((coq / 'C/jet_contracts.expected').read_text(), r1, d1)
    old_keys = {k for k, _ in old}
    if [(k, t) for k, t in new if k in old_keys] != old:
        raise ValueError('inherited contract bytes/order changed')
    added = [(k, t) for k, t in new if k not in old_keys]
    if len(added) != 37 or len(r1) - len(r0) != 34 or len(d1) - len(d0) != 3:
        raise ValueError('unexpected Version result/definition inventory')
    report = (candidate / 'new_contracts.out').read_text()
    marks = list(re.finditer(r'(?m)^VERSION_DEEP_(TYPE|DEF) (\S+)\n', report))
    if [(m[1], m[2]) for m in marks] != [(k, mod + '.' + n) for (k, mod, n, _), _ in added]:
        raise ValueError('missing/reordered deep records')
    for i, (_, text) in enumerate(added):
        full = report[marks[i].end():marks[i+1].start() if i+1 < len(marks) else len(report)]
        if '...' in full:
            raise ValueError('truncated deep record')
        short, long = re.sub(r'\s+', '', text), re.sub(r'\s+', '', full)
        if short == long:
            continue
        position = 0
        fragments = short.split('...')
        for j, frag in enumerate(fragments):
            offset = len(long) - len(frag) if j == len(fragments)-1 and long.endswith(frag) else long.find(frag, position)
            if offset < position or j == 0 and offset != 0:
                raise ValueError('compact/deep record disagreement')
            position = offset + len(frag)
        if '...' not in short or position != len(long):
            raise ValueError('unexplained deep/compact difference')
    dep0 = nullable.dependencies((MAIN / 'C/jet_assumptions.expected').read_text())
    dep1 = nullable.dependencies((coq / 'C/jet_assumptions.expected').read_text())
    if {name: dep1.get(name) for name in dep0} != dep0:
        raise ValueError('inherited dependencies changed')
    if {name: deps for name, deps in dep1.items() if name not in dep0} != receipt['expected_dependencies']:
        raise ValueError('new dependencies differ from independent checks')
    for stem in ['new_contracts'] + ['compile-' + Path(e['file']).stem for e in sourcing['modules']]:
        if (candidate / (stem + '.err')).read_bytes():
            raise ValueError('fresh compilation diagnostics')
    terminal = json.loads((candidate / 'KERNEL.json').read_text())
    if terminal['exit_code'] != 0 or terminal['log_sha256'] != patch.sha((candidate / 'new_kernel.log').read_bytes()):
        raise ValueError('kernel exit/log evidence drift')
    load('version_review_kernel', HERE.parent / 'scalar-mul/review.py').kernel(
        (candidate / 'new_kernel.log').read_text(), sorted((MAIN / 'C/jet_coqchk_axioms.expected').read_text().split()))
    return {'candidate': str(candidate), 'new_results': 34, 'new_definitions': 3, 'coverage_added': 1,
            'inherited_contract_records_byte_identical': len(old), 'inherited_dependencies_unchanged': len(dep0),
            'fresh_closure_kernel_checked': True, 'deep_new_records_checked': True,
            'snapshots_sha256': {n: patch.sha((coq / n).read_bytes()) for n in FILES},
            'preexisting_staged_patch_sha256': meta['main_staged_patch_sha256'],
            'normal_main_acceptance': False, 'main_installation': False}


def install(candidate):
    result = review(candidate)
    patch.patch_files({MAIN / name: (candidate / 'Coq' / name).read_text() for name in FILES})
    if patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != result['preexisting_staged_patch_sha256']:
        raise ValueError('original staging changed during install')
    result['main_installation'] = True
    result['next'] = 'Freeze main audit inputs and run check-jets.sh --accept without update/no-build flags.'
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('mode', choices=['assemble', 'prepare', 'kernel', 'review', 'install'])
    cli.add_argument('--candidate', type=Path); args = cli.parse_args()
    if args.mode != 'assemble' and args.candidate is None:
        cli.error('--candidate required')
    if args.mode == 'assemble': assemble()
    elif args.mode == 'prepare': prepare(args.candidate.resolve())
    elif args.mode == 'kernel': kernel(args.candidate.resolve())
    elif args.mode == 'review': print(json.dumps(review(args.candidate.resolve()), indent=2))
    else: install(args.candidate.resolve())
