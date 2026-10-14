"""Frozen two-getter import and preserving normal admission.

Reuse Version's snapshot printer/reconciliation with explicit batch counts
and roots. Only the new module sources and seven registry files are installed;
existing staging stays unchanged. Normal acceptance is a separate final run.
"""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import importlib.util

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location('getter_admission_base', HERE.parent / 'elements-version-admission/admission.py')
base = importlib.util.module_from_spec(spec); spec.loader.exec_module(base)
COMMIT = '30404face45383153528f36d915de6d7df11f3f4'
NAMES = ['jet_elements_getter32_exec', 'jet_elements_getter32_layout', 'jet_elements_locktime_local',
         'jet_elements_current_index_exec', 'jet_elements_current_index_layout', 'jet_elements_current_index_local']
COVERAGE = ('simplicity_lock_time C.jet_elements_locktime_local elements_locktime_local_spec\n'
            'simplicity_current_index C.jet_elements_current_index_local elements_current_index_local_spec\n')
scanner = base.load('getter_source_scanner', REPO / 'Coq/scan-jet-proofs.py')


def provenance():
    sourcing = json.loads((HERE / 'SOURCE.json').read_text())
    for e in sourcing['modules']:
        raw = subprocess.check_output(['git', 'show', COMMIT + ':Coq/C/' + e['file']], cwd=REPO)
        if base.patch.sha(raw) != e['source_sha256'] or (REPO / 'Coq/C' / e['file']).read_bytes() != raw:
            raise ValueError('frozen getter source drift')
    for path, value in sourcing['inherited_sha256'].items():
        if base.patch.sha((REPO / path).read_bytes()) != value: raise ValueError('inherited getter source drift')
    receipt = {'expected_dependencies': {}}
    if (HERE / 'INDEPENDENT.json').exists():
        receipt['expected_dependencies'] = json.loads((HERE / 'INDEPENDENT.json').read_text())['expected_dependencies']
    base.NEW_RESULTS = sum(len(e['results']) for e in sourcing['modules'])
    base.NEW_DEFINITIONS = len(sourcing['definitions'])
    return sourcing, receipt


base.HERE = HERE
base.COVERAGE = COVERAGE
base.COVERAGE_ADDED = 2
base.KERNEL_ROOTS = ['C.jet_elements_locktime_local', 'C.jet_elements_current_index_local']
base.provenance = provenance


def assemble():
    entries, changes, inherited = [], {}, {}
    for name in NAMES:
        raw = subprocess.check_output(['git', 'show', COMMIT + ':Coq/C/' + name + '.v'], cwd=REPO)
        text = raw.decode(); code = scanner.code_only(text)
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit|vm_cast_no_check|native_cast_no_check)\b', code):
            raise ValueError('forbidden proof construct')
        path = REPO / 'Coq/C' / (name + '.v')
        if path.exists() and path.read_bytes() != raw: raise ValueError('source collision')
        if not path.exists(): changes[path] = text
        entries.append({'file': name + '.v', 'module': 'C.' + name, 'source_sha256': base.patch.sha(raw),
                        'results': re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M),
                        'definitions': re.findall(r'^Definition\s+(\w+)', code, re.M)})
        for dep in set(re.findall(r'\bC\.(\w+)', code)) - set(NAMES):
            p = REPO / 'Coq/C' / (dep + '.v')
            frozen = subprocess.check_output(['git', 'show', COMMIT + ':Coq/C/' + dep + '.v'], cwd=REPO)
            if p.read_bytes() != frozen: raise ValueError('shared/main dependency collision: ' + dep)
            inherited['Coq/C/' + dep + '.v'] = base.patch.sha(frozen)
    definitions = [e['module'] + '.' + n for e in entries for n in e['definitions']]
    sourcing = {'shared_commit': COMMIT, 'modules': entries, 'definitions': definitions, 'inherited_sha256': inherited}
    changes[HERE / 'SOURCE.json'] = json.dumps(sourcing, indent=2) + '\n'
    base.patch.patch_files(changes)
    work = Path(tempfile.mkdtemp(prefix='jet-elements-getters.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    shutil.copytree(base.MAIN, coq, symlinks=True)
    for name in ['C', 'Haskell']: (work / name).symlink_to(REPO / name, target_is_directory=True)
    extensions = {'_CoqProject': ['C/' + e['file'] for e in entries],
                  '_CoqProject.jets': ['C/' + e['file'] for e in entries],
                  'C/jet_public_theorems.txt': [e['module'] + ' ' + n for e in entries for n in e['results']],
                  'C/jet_contract_definitions.txt': [e['module'] + ' ' + n for e in entries for n in e['definitions']]}
    changes = {}
    for name, rows in extensions.items():
        text = (base.MAIN / name).read_text()
        if any(row in text.splitlines() for row in rows) or not text.endswith('\n'): raise ValueError('nonfresh registry')
        changes[coq / name] = text + '\n'.join(rows) + '\n'
    text = (base.MAIN / 'C/jet_coverage.tsv').read_text()
    if any(row.split()[0] in {'simplicity_lock_time', 'simplicity_current_index'} for row in text.splitlines() if row.strip() and not row.startswith('#')):
        raise ValueError('getter already covered')
    changes[coq / 'C/jet_coverage.tsv'] = text + COVERAGE
    meta = {'candidate': str(work), 'extensions': extensions,
            'main_metadata_sha256': {n: base.patch.sha((base.MAIN / n).read_bytes()) for n in base.FILES},
            'main_index_sha256': {n: base.patch.sha(subprocess.check_output(['git', 'show', ':Coq/' + n], cwd=REPO)) for n in base.FILES},
            'main_staged_patch_sha256': base.patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)),
            'source_sha256': {'Coq/C/' + e['file']: e['source_sha256'] for e in entries}, 'full_acceptance': False}
    changes[work / 'ASSEMBLY.json'] = json.dumps(meta, indent=2) + '\n'
    base.patch.patch_files(changes)
    print(json.dumps({'candidate': str(work), 'modules': 6, 'results': sum(len(e['results']) for e in entries), 'definitions': len(definitions)}, indent=2))


def prepare(candidate):
    sourcing, _ = provenance()
    for e in sourcing['modules']:
        base.run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', 'C/' + e['file']], 'compile-' + Path(e['file']).stem)
    driver = ['Set Warnings "-notation-overridden".'] + ['Require ' + e['module'] + '.' for e in sourcing['modules']]
    for e in sourcing['modules']:
        for name in e['results']:
            full = e['module'] + '.' + name
            driver += ['Goal True. idtac "JET_ASSUMPTIONS ' + full + '". exact I. Qed.', 'Print Assumptions ' + full + '.']
    base.patch.patch_files({candidate / 'new_assumptions.v': '\n'.join(driver) + '\n'})
    base.run(candidate, ['bash', 'build-jets.sh', '--coqc', '-q', str(candidate / 'new_assumptions.v')], 'new_assumptions')
    deps = base.normal.assumptions((candidate / 'new_assumptions.out').read_text())
    wanted = {e['module'] + '.' + n for e in sourcing['modules'] for n in e['results']}
    if set(deps) != wanted: raise ValueError('assumption inventory mismatch')
    receipt = {'expected_dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'normal_acceptance': False}
    base.patch.patch_files({HERE / 'INDEPENDENT.json': json.dumps(receipt, indent=2) + '\n'})
    base.prepare(candidate)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('mode', choices=['assemble', 'prepare', 'review', 'install'])
    cli.add_argument('--candidate', type=Path); args = cli.parse_args()
    if args.mode == 'assemble': assemble()
    else:
        if args.candidate is None: cli.error('--candidate required')
        candidate = args.candidate.resolve()
        if args.mode == 'prepare': prepare(candidate)
        elif args.mode == 'review': print(json.dumps(base.review(candidate), indent=2))
        else: base.install(candidate)
