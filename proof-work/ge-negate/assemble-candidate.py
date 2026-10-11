"""Guarded isolated assembly through apply_patch; never edit the baseline.

This adds provisional registries, not accepted coverage. All inherited sources
and snapshots must stay byte-identical until normal-build audit generation.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(archive):
    receipt = json.loads((archive / 'ASSEMBLY.json').read_text())
    source = Path(receipt['baseline']) / 'Coq'
    target = Path(receipt['candidate']) / 'Coq'
    for item in receipt['files']:
        for root, key in [(source, 'baseline_sha256'), (target, 'candidate_sha256')]:
            if sha(root / item['path']) != item[key]:
                raise ValueError('metadata hash changed: ' + str(root / item['path']))
    inherited = sorted(source.glob('C/*.v'))
    if len(inherited) != receipt['inherited_sources_byte_identical']:
        raise ValueError('inherited source count changed')
    for p in inherited:
        if p.read_bytes() != (target / 'C' / p.name).read_bytes():
            raise ValueError('inherited source changed: ' + p.name)
    manifest = json.loads((archive / 'manifest.json').read_text())
    for entry in manifest['files']:
        name = entry['materialized_name']
        relative = ('C/' if name.endswith('.v') else 'ge-negate-review/') + name
        if sha(archive / entry['path']) != entry['sha256'] or sha(target / relative) != entry['sha256']:
            raise ValueError('new archived/materialized source changed: ' + name)
    return {'metadata_hashes': len(receipt['files']), 'inherited_v_sources': len(inherited),
            'new_module_hashes': 38, 'new_checker_hashes': 2, 'unchanged': True}


def assemble(base, candidate, archive):
    base, candidate, archive = [p.resolve() for p in (base, candidate, archive)]
    if base == candidate or not str(candidate).startswith('/private/tmp/'):
        raise ValueError('candidate must be a separate temporary directory')
    source = base / 'Coq'
    target = candidate / 'Coq'
    manifest = json.loads((archive / 'manifest.json').read_text())
    inherited = sorted(source.glob('C/*.v'))
    if len(inherited) != 923:
        raise ValueError('unexpected inherited module count')
    for p in inherited:
        if p.read_bytes() != (target / 'C' / p.name).read_bytes():
            raise ValueError('inherited source changed: ' + p.name)
    additions = {}
    modules = []
    for entry in manifest['files']:
        p = archive / entry['path']
        if sha(p) != entry['sha256']:
            raise ValueError('archive hash mismatch: ' + str(p))
        name = entry['materialized_name']
        relative = ('C/' if name.endswith('.v') else 'ge-negate-review/') + name
        if (target / relative).exists():
            raise ValueError('new source already exists: ' + relative)
        additions[relative] = p.read_text()
        if name.endswith('.v'):
            modules.append('C/' + name)
    if len(modules) != 38 or len(additions) != 40:
        raise ValueError('unexpected new proof/checker count')
    originals = {}
    replacements = {}

    def original(name):
        text = (source / name).read_text()
        if text != (target / name).read_text():
            raise ValueError('candidate metadata already differs: ' + name)
        originals[name] = text
        return text

    def extend(name, extra, expected_rows):
        text = original(name)
        old = {l.strip() for l in text.splitlines() if l.strip() and not l.startswith('#')}
        rows = [l.strip() for l in extra.splitlines() if l.strip() and not l.startswith('#')]
        if len(rows) != expected_rows or len(set(rows)) != len(rows) or old & set(rows):
            raise ValueError('invalid inventory extension: ' + name)
        if not text.endswith('\n') or not extra.endswith('\n'):
            raise ValueError('inventory must have terminal newline')
        replacements[name] = text + extra

    extend('_CoqProject', '\n'.join(modules) + '\n', 38)
    extend('_CoqProject.jets', '\n'.join(modules) + '\n', 38)
    extend('C/jet_public_theorems.txt', (archive / 'public-results.txt.source').read_text(), 109)
    extend('C/jet_contract_definitions.txt', (archive / 'contract-definitions.txt.source').read_text(), 37)
    extend('C/jet_coverage.tsv',
           'simplicity_ge_negate\tC.jet_secp_ge_negate_local\tge_negate_literal_local_spec\n', 1)

    def replace_once(name, old, new):
        text = original(name)
        if text.count(old) != 1:
            raise ValueError('metadata replacement is not unique: ' + name)
        replacements[name] = text.replace(old, new)

    replace_once('jet-coverage.py',
                 '"simplicity_gej_is_infinity", "simplicity_gej_negate"}',
                 '"simplicity_gej_is_infinity", "simplicity_gej_negate", "simplicity_ge_negate"}')
    point_tuple = '            ("jet_secp_gej_negate_local.v", "gej_negate_literal_local_spec", "simplicity_gej_negate"),\n'
    replace_once('test-jet-coverage.py', point_tuple, point_tuple +
                 '            ("jet_secp_ge_negate_local.v", "ge_negate_literal_local_spec", "simplicity_ge_negate"),\n')
    hook = 'python3 gej-negate-review/test-gej-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C\n'
    replace_once('check-jets.sh', hook, hook +
                 'python3 ge-negate-review/check-ge-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C\n' +
                 'python3 ge-negate-review/test-ge-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C\n')
    if len(replacements) != 8:
        raise ValueError('unexpected infrastructure change count')
    patch = ['*** Begin Patch']
    for name, content in additions.items():
        patch.append('*** Add File: ' + str(target / name))
        patch.extend('+' + line for line in content.splitlines())
    for name, content in replacements.items():
        patch.append('*** Update File: ' + str(target / name))
        diff = list(difflib.unified_diff(originals[name].splitlines(), content.splitlines(), n=3))[2:]
        patch.extend('@@' if line.startswith('@@') else line for line in diff)
    patch.append('*** End Patch')
    subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True,
                   check=True, stdout=subprocess.DEVNULL)
    for p in inherited:
        if p.read_bytes() != (target / 'C' / p.name).read_bytes():
            raise ValueError('inherited source changed after patch: ' + p.name)
    for name, content in additions.items():
        if (target / name).read_text() != content:
            raise ValueError('materialized source mismatch: ' + name)
    snapshots = ['C/jet_contracts.expected', 'C/jet_assumptions.expected']
    for name in snapshots:
        if (source / name).read_bytes() != (target / name).read_bytes():
            raise ValueError('inherited snapshot changed: ' + name)
    return {'baseline': str(base), 'candidate': str(candidate),
            'baseline_full_acceptance': '77601 still live; no acceptance inferred',
            'full_acceptance': False, 'inherited_sources_byte_identical': len(inherited),
            'new_modules': len(modules), 'new_checkers': len(additions) - len(modules),
            'new_results': 109, 'new_definitions': 37, 'new_coverage_entries': 1,
            'snapshots_unchanged': True,
            'files': [{'path': n, 'baseline_sha256': sha(source / n),
                       'candidate_sha256': sha(target / n)} for n in replacements]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.verify:
        result = verify(args.archive)
    else:
        if args.baseline is None or args.candidate is None:
            parser.error('assembly requires --baseline and --candidate')
        result = assemble(args.baseline, args.candidate, args.archive)
    print(json.dumps(result, indent=2))
