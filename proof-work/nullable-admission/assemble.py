"""Prepare an isolated nullable-tappath admission preserving main's registries.

Only a fresh temporary candidate is changed. Existing proof sources, metadata
and staging in the main checkout are read, never rewritten by this command.
"""
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
MAIN = REPO / 'Coq'
FILES = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
         'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv',
         'C/jet_assumptions.expected', 'C/jet_contracts.expected']
OLD = 'simplicity_bitcoin_tappath C.jet_bitcoin_raw_jets bitcoin_tappath_raw_local_spec'
NEW = 'simplicity_bitcoin_tappath C.jet_bitcoin_tappath_nullable_raw bitcoin_tappath_nullable_raw_local_spec'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def patch_files(changes):
    lines = ['*** Begin Patch']
    for path, content in changes.items():
        if path.exists():
            diff = list(difflib.unified_diff(path.read_text().splitlines(), content.splitlines(), n=3))[2:]
            if not diff:
                continue
            lines.append('*** Update File: ' + str(path))
            lines += ['@@' if row.startswith('@@') else row for row in diff]
        else:
            lines.append('*** Add File: ' + str(path))
            lines += ['+' + row for row in content.splitlines()]
    lines.append('*** End Patch')
    subprocess.run(['apply_patch'], input='\n'.join(lines) + '\n', text=True, check=True,
                   stdout=subprocess.DEVNULL)


def assemble():
    entries = json.loads((REPO / 'proof-work/shared-foundations-integration/manifest.json').read_text())['modules'][-2:]
    original = {name: (MAIN / name).read_bytes() for name in FILES}
    index = {name: sha(subprocess.check_output(['git', 'show', ':Coq/' + name], cwd=REPO)) for name in FILES}
    staged = sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO))
    work = Path(tempfile.mkdtemp(prefix='jet-nullable-admission.', dir='/tmp'))
    target = work / 'Coq'
    shutil.copytree(MAIN, target, symlinks=True)
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    changes = {}
    extensions = {
        '_CoqProject': [str(Path(entry['path']).relative_to('Coq')) for entry in entries],
        '_CoqProject.jets': [str(Path(entry['path']).relative_to('Coq')) for entry in entries],
        'C/jet_public_theorems.txt': ['C.' + Path(entry['path']).stem + ' ' + name
                                    for entry in entries for name in entry['results']],
        'C/jet_contract_definitions.txt': ['C.' + Path(entry['path']).stem + ' ' + name
                                         for entry in entries for name in entry['definitions']],
    }
    for name, rows in extensions.items():
        content = original[name].decode()
        if not content.endswith('\n') or any(row in content.splitlines() for row in rows):
            raise ValueError('non-fresh inventory extension: ' + name)
        changes[target / name] = content + '\n'.join(rows) + '\n'
    content = original['C/jet_coverage.tsv'].decode()
    matches = [line for line in content.splitlines() if ' '.join(line.split()) == OLD]
    if len(matches) != 1:
        raise ValueError('expected exactly the original tappath coverage row')
    changes[target / 'C/jet_coverage.tsv'] = content.replace(matches[0], NEW, 1)
    patch_files(changes)
    for entry in entries:
        if sha((target / Path(entry['path']).relative_to('Coq')).read_bytes()) != entry['sha256']:
            raise ValueError('nullable source drift')
    for name, raw in original.items():
        if (MAIN / name).read_bytes() != raw:
            raise ValueError('main registry changed while assembling')
    if sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != staged:
        raise ValueError('main staging changed while assembling')
    meta = {'format': 1, 'candidate': str(work), 'main_head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip(),
            'main_metadata_sha256': {name: sha(raw) for name, raw in original.items()},
            'main_index_sha256': index, 'main_staged_patch_sha256': staged,
            'extensions': extensions, 'old_coverage_row': OLD, 'new_coverage_row': NEW,
            'source_sha256': {entry['path']: entry['sha256'] for entry in entries},
            'normal_registration_candidate': True, 'full_acceptance': False, 'coverage_added': 0}
    patch_files({work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    print(json.dumps(meta, indent=2))
    return meta


if __name__ == '__main__':
    assemble()
