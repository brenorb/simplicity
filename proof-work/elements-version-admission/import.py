"""Import only the frozen, independently reviewed Elements Version closure.

All durable source writes use apply_patch. Existing sources must match the
review baseline or the exact imported bytes; other Claude work is untouched.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location('version_patch', HERE.parent / 'nullable-admission/assemble.py')
patch = importlib.util.module_from_spec(spec); spec.loader.exec_module(patch)


def main():
    sourcing = json.loads((HERE.parent / 'elements-version-review/SOURCING.json').read_text())
    for name, value in sourcing['inherited_dependency_hashes'].items():
        if patch.sha((REPO / 'Coq/C' / (name + '.v')).read_bytes()) != value:
            raise ValueError('inherited source drift: ' + name)
    changes = {}
    for entry in sourcing['modules']:
        path = 'Coq/C/' + entry['file']
        raw = subprocess.check_output(['git', 'show', sourcing['shared_commit'] + ':' + path], cwd=REPO)
        if patch.sha(raw) != entry['source_sha256']:
            raise ValueError('frozen blob changed: ' + path)
        target = REPO / path
        if target.exists() and target.read_bytes() != raw:
            raise ValueError('import would overwrite different source: ' + path)
        if not target.exists():
            changes[target] = raw.decode()
    unit = REPO / 'Coq/C/jet_elements_translation_unit.c'
    if patch.sha(unit.read_bytes()) not in {sourcing['baseline_translation_unit_sha256'], sourcing['translation_unit_sha256']}:
        raise ValueError('preparatory TU has unrelated changes')
    raw = subprocess.check_output(['git', 'show', sourcing['shared_commit'] + ':Coq/C/jet_elements_translation_unit.c'], cwd=REPO)
    if patch.sha(raw) != sourcing['translation_unit_sha256']:
        raise ValueError('translation-unit blob drift')
    changes[unit] = raw.decode()
    before = patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO))
    patch.patch_files(changes)
    if patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != before:
        raise ValueError('preexisting staging changed')
    for entry in sourcing['modules']:
        if patch.sha((REPO / 'Coq/C' / entry['file']).read_bytes()) != entry['source_sha256']:
            raise ValueError('imported source drift')
    print(json.dumps({'imported_modules': len(sourcing['modules']), 'frozen_commit': sourcing['shared_commit'],
                      'byte_identical': True, 'index_preserved': True, 'normal_admission': False}, indent=2))


if __name__ == '__main__':
    main()
