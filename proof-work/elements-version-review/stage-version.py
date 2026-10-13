"""Stage a frozen Claude version-proof closure for independent normal checking.

Only a fresh scratch candidate is written, through apply_patch; no main,
shared-worktree, registry or live lambda-audit source is modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
REPO = ARCHIVE.parent.parent
SHARED = REPO.parent / 'simplicity-shared'
COMMIT = 'adff42d3365d759a988740d520c45c9d286a51ab'
BASE = Path('/tmp/jet-scalar-square-integration.MAhL2g/Coq')
ROOT = 'jet_elements_version_local'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(path):
    result = subprocess.run(['git', 'show', COMMIT + ':Coq/C/' + path],
                            cwd=SHARED, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return result.stdout


def stage(candidate, verify=False):
    candidate = candidate.resolve()
    if not str(candidate).startswith('/private/tmp/jet-elements-version-review.') or candidate == BASE.parent:
        raise ValueError('candidate must be a dedicated fresh temporary tree')
    target = candidate / 'Coq'
    if not target.is_dir() or (not verify and (target / 'C' / (ROOT + '.v')).exists()):
        raise ValueError('candidate is not a fresh unassembled baseline')
    for path in BASE.rglob('*.v'):
        if path.read_bytes() != (target / path.relative_to(BASE)).read_bytes():
            raise ValueError('inherited source drift')
    visited, active, entries, inherited = set(), set(), [], {}
    # Reuse the accepted scanner rather than treating comments as code/imports.
    import importlib.util
    spec = importlib.util.spec_from_file_location('elements_source_scanner', BASE / 'scan-jet-proofs.py')
    scanner = importlib.util.module_from_spec(spec); spec.loader.exec_module(scanner)

    def visit(name):
        if name in visited:
            return
        raw = blob(name + '.v'); path = BASE / 'C' / (name + '.v')
        if path.exists():
            if path.read_bytes() != raw:
                raise ValueError('shared/inherited source collision: ' + name)
            inherited[name] = sha(raw); visited.add(name); return
        if name in active:
            raise ValueError('cyclic new dependency: ' + name)
        active.add(name)
        code = scanner.code_only(raw.decode())
        if re.search(r'\b(?:Axiom|Parameter|Admitted|admit)\b', code):
            raise ValueError('assumed/skipped proof: ' + name)
        for dep in sorted(set(re.findall(r'\bC\.(\w+)', code))):
            visit(dep)
        entries.append({'file': name + '.v', 'module': 'C.' + name,
                        'source_sha256': sha(raw), 'source_bytes': len(raw),
                        'results': re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M),
                        'source': raw.decode()})
        active.remove(name); visited.add(name)

    visit(ROOT)
    patch = ['*** Begin Patch']
    for entry in entries:
        patch += ['*** Add File: ' + str(target / 'C' / entry['file'])]
        patch += ['+' + line for line in entry['source'].splitlines()]
    # The committed Elements unit includes real SHA/ops helpers internally.
    # The accepted old baseline's preparatory unit did not. This is an
    # explicit scratch-only TU update, never a production C substitution.
    import difflib
    unit = 'jet_elements_translation_unit.c'
    old_unit = (BASE / 'C' / unit).read_text()
    new_unit = blob(unit).decode()
    patch.append('*** Update File: ' + str(target / 'C' / unit))
    diff = list(difflib.unified_diff(old_unit.splitlines(), new_unit.splitlines(), n=3))[2:]
    patch += ['@@' if line.startswith('@@') else line for line in diff]
    patch.append('*** End Patch')
    if not verify:
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    for entry in entries:
        if sha((target / 'C' / entry['file']).read_bytes()) != entry['source_sha256']:
            raise ValueError('staged source drift')
    if (target / 'C' / unit).read_text() != new_unit:
        raise ValueError('derived translation unit drift')
    return {'format': 1, 'shared_commit': COMMIT, 'baseline_coq': str(BASE.resolve()),
            'candidate': str(candidate), 'root': 'C.' + ROOT,
            'modules': [{k: v for k, v in e.items() if k != 'source'} for e in entries],
            'inherited_dependency_hashes': inherited,
            'translation_unit_sha256': sha(new_unit.encode()),
            'baseline_translation_unit_sha256': sha(old_unit.encode()),
            'namespace_only_change': False, 'byte_identical_to_frozen_commit': True,
            'normal_registration': False, 'full_acceptance': False, 'checkout_coverage_added': 0,
            'scope': 'Independent recheck of selected version proof; primitive semantics/source correspondence and AST regeneration still require review.'}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--candidate', type=Path, required=True)
    cli.add_argument('--verify', action='store_true')
    args = cli.parse_args(); print(json.dumps(stage(args.candidate, args.verify), indent=2))

