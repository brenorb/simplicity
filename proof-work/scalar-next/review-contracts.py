"""Read-only review of all scalar helper types/definitions and deep prints.

Retained ellipsis fragments are only diagnostics, never proofs of omitted
term equality. The independently checked actual sources remain essential.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    'contract_parser', Path(__file__).resolve().parent.parent / 'ge-negate/review-preliminary.py')
parser = importlib.util.module_from_spec(spec)
spec.loader.exec_module(parser)


def retained(ordinary, deep):
    parts = parser.norm(ordinary).split('...')
    deep = parser.norm(deep)
    end = len(deep) - len(parts[-1])
    if not deep.endswith(parts[-1]):
        return False
    position = 0
    for i, fragment in enumerate(parts[:-1]):
        offset = deep.find(fragment, position, end)
        if offset < 0 or (i == 0 and offset != 0):
            return False
        position = offset + len(fragment)
    # Anchor the final retained fragment to the end, rather than selecting
    # an earlier identical run of closing parentheses in a binary numeral.
    return position <= end


def review(archive, work):
    prior = json.loads((archive / 'CONTRACT-REVIEW.json').read_text())
    for filename, digest in prior['output_hashes'].items():
        if hashlib.sha256((work / filename).read_bytes()).hexdigest() != digest:
            raise ValueError('reviewed print hash changed: ' + filename)
    for filename in ['contracts-standard.err', 'contracts-deep.err']:
        if (work / filename).read_text():
            raise ValueError('nonempty diagnostics: ' + filename)
    manifest = json.loads((archive / 'manifest.json').read_text())
    for entry in manifest['modules']:
        source = (work / entry['file']).read_bytes()
        if (hashlib.sha256(source).hexdigest() != entry['sha256']
                or source != (archive / entry['path']).read_bytes()):
            raise ValueError('actual source hash changed: ' + entry['file'])
    types = parser.rows(archive / 'public-results.txt.source')
    definitions = parser.rows(archive / 'contract-definitions.txt.source')
    if len(types) != 86 or len(definitions) != 64:
        raise ValueError('unexpected print inventories')
    ordinary = (work / 'contracts-standard.out').read_text()
    deep = (work / 'contracts-deep.out').read_text()
    if '...' in deep:
        raise ValueError('deep report still truncated')
    result = {}
    for label, parse, rows in [('types', parser.types, types),
                               ('definitions', parser.definitions, definitions)]:
        a, b = parse(ordinary, rows), parse(deep, rows)
        changed = {name for name in a if parser.norm(a[name]) != parser.norm(b[name])}
        if changed != set(prior['contracts'][label]['deep_supplements']):
            raise ValueError('unexpected supplement inventory: ' + label)
        for name in changed:
            if '...' not in a[name] or not retained(a[name], b[name]):
                raise ValueError('non-ellipsis print difference: ' + name)
        result[label] = {'count': len(a), 'exact_whitespace_normalized': len(a) - len(changed),
                         'deep_supplements': sorted(changed)}
    if result != prior['contracts']:
        raise ValueError('reviewed contract counts changed')
    return {'contracts': result, 'full_acceptance': False, 'public_coverage_added': 0}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--archive', type=Path, default=Path(__file__).resolve().parent)
    cli.add_argument('--work', type=Path, required=True)
    args = cli.parse_args()
    print(json.dumps(review(args.archive, args.work), indent=2))
