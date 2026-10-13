"""Exact public scalar-multiply closure transport; preparation is not acceptance.

Only namespace references and normal-namespace registration are adapted.
Sources/metadata are materialized exclusively through apply_patch. Never writes
the accepted baseline or main checkout registries, and never updates snapshots.
"""
import argparse
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
PREFIXES = ('MulC.', 'LifeC.', 'PubC.', 'OwnC.')
ROOT = 'jet_secp_scalar_multiply_local'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def transport(text):
    for prefix in PREFIXES:
        text = text.replace(prefix, 'C.')
    return text


def no_audit_footer(text):
    return re.sub(r'^Print Assumptions.*\n', '', text, flags=re.M).strip()


def module_records(value):
    if isinstance(value, dict):
        if all(k in value for k in ['file', 'sha256', 'results']) and (
                'module' in value or isinstance(value.get('name'), str)
                and value['name'].startswith(PREFIXES)):
            yield {**value, 'module': value.get('module', value.get('name'))}
        else:
            for child in value.values():
                yield from module_records(child)
    elif isinstance(value, list):
        for child in value:
            yield from module_records(child)


def provenance():
    entries = {}
    for directory in sorted(ARCHIVE.parent.iterdir()):
        if not directory.is_dir() or not directory.name.startswith(('scalar-mul', 'scalar-reduce512')):
            continue
        for document in sorted(directory.glob('*.json')):
            for entry in module_records(json.loads(document.read_text())):
                source = directory / (entry['file'] + '.source')
                if not source.exists():
                    continue
                raw = source.read_bytes()
                if digest(raw) != entry['sha256']:
                    raise ValueError('archived source drift: ' + str(source))
                if entry['module'] in entries:
                    if entries[entry['module']]['original_sha256'] != entry['sha256']:
                        raise ValueError('ambiguous archived module: ' + entry['module'])
                    continue
                entries[entry['module']] = {
                    'name': entry['file'][:-2], 'original_module': entry['module'],
                    'archive': str(source.resolve()), 'family': directory.name,
                    'original_sha256': entry['sha256'], 'results': entry['results'],
                    'definitions': entry.get('definitions', []), 'text': raw.decode()}
    return entries


def plan(base):
    base = base.resolve()
    parent = ARCHIVE.parent / 'scalar-add-integration'
    accepted = json.loads((parent / 'ACCEPTANCE.json').read_text())
    if base != Path(accepted['candidate']).resolve() or accepted['exit_code'] != 0:
        raise ValueError('baseline is not the terminal accepted scalar-add candidate')
    if digest(Path(accepted['log']).read_bytes()) != accepted['log_sha256']:
        raise ValueError('parent terminal acceptance log drift')
    load('multiply_checked_parent', parent / 'review-normal.py').review()
    load('multiply_checked_public', ARCHIVE.parent / 'scalar-multiply-public/review.py').review()
    audit = load('multiply_inputs', base / 'Coq/jet-audit-inputs.py')
    fingerprint = audit.fingerprint(base / 'Coq', REPO)
    if fingerprint != accepted['audit_input_sha256']:
        raise ValueError('accepted parent fingerprint drift')
    entries, order, inherited, visited, active = provenance(), [], {}, set(), set()

    def visit(key):
        prefix, name = key.split('.', 1)
        path = base / 'Coq/C' / (name + '.v')
        if path.exists():
            raw = path.read_bytes()
            exception = False
            if key in entries:
                transported = transport(entries[key]['text'])
                if transported.encode() != raw:
                    if no_audit_footer(transported) != no_audit_footer(raw.decode()):
                        raise ValueError('inherited source differs beyond audit footer: ' + key)
                    exception = True
            inherited[name] = {'sha256': digest(raw), 'reuse_audit_footer_only': exception}
            return
        if key in visited:
            return
        if key in active or key not in entries:
            raise ValueError('cycle or unarchived dependency: ' + key)
        active.add(key)
        entry = entries[key]
        for namespace, dep in sorted(set(re.findall(r'\b(MulC|LifeC|PubC|OwnC|C)\.(\w+)', entry['text']))):
            visit(namespace + '.' + dep)
        results = re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', entry['text'], re.M)
        if results != entry['results']:
            raise ValueError('result inventory drift: ' + key)
        text = transport(entry['text'])
        if any(e['name'] == name for e in order):
            raise ValueError('normal namespace module collision: ' + name)
        order.append({**entry, 'text': text, 'candidate_sha256': digest(text.encode())})
        active.remove(key)
        visited.add(key)

    visit('OwnC.' + ROOT)
    return {'baseline': str(base), 'baseline_fingerprint': fingerprint,
            'baseline_full_acceptance_required': True, 'modules': order,
            'inherited_dependency_hashes': inherited,
            'excluded_unselected_modules': sorted(set(entries) - visited),
            'full_acceptance': False, 'checkout_coverage_added': 0}


def assemble(base, candidate, verify=False):
    planned = plan(base)
    candidate, base = candidate.resolve(), base.resolve()
    if not str(candidate).startswith('/private/tmp/') or candidate == base:
        raise ValueError('candidate must be a separate temporary directory')
    source, target = base / 'Coq', candidate / 'Coq'
    for sibling in ['C', 'Haskell']:
        if not (candidate / sibling).is_symlink() or (candidate / sibling).resolve() != (REPO / sibling).resolve():
            raise ValueError('candidate lacks verified source layout: ' + sibling)
    for path in source.rglob('*.v'):
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited candidate source changed')
    additions = {'C/' + entry['name'] + '.v': entry['text'] for entry in planned['modules']}
    if not verify and any((target / name).exists() for name in additions):
        raise ValueError('candidate already assembled')
    for name in ['check-multiply-public.py', 'test-multiply-public.py']:
        additions['scalar-multiply-review/' + name] = (ARCHIVE / name).read_text()
    originals, replacements = {}, {}

    def original(name):
        content = (source / name).read_text()
        if not verify and content != (target / name).read_text():
            raise ValueError('candidate metadata changed before assembly: ' + name)
        originals[name] = content
        return content

    def extend(name, rows):
        content = original(name)
        old = {line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')}
        if old & set(rows) or len(rows) != len(set(rows)) or not content.endswith('\n'):
            raise ValueError('invalid inventory extension: ' + name)
        replacements[name] = content + '\n'.join(rows) + '\n'

    entries = planned['modules']
    paths = ['C/' + entry['name'] + '.v' for entry in entries]
    results = ['C.' + entry['name'] + ' ' + name for entry in entries for name in entry['results']]
    definitions = ['C.' + entry['name'] + ' ' + name for entry in entries for name in entry['definitions']]
    extend('_CoqProject', paths)
    extend('_CoqProject.jets', paths)
    extend('C/jet_public_theorems.txt', results)
    extend('C/jet_contract_definitions.txt', definitions)
    extend('C/jet_coverage.tsv', ['simplicity_scalar_multiply\tC.' + ROOT + '\tscalar_multiply_literal_local_spec'])
    for name, old, new in [
        ('jet-coverage.py', '"simplicity_scalar_add"}:', '"simplicity_scalar_add", "simplicity_scalar_multiply"}:'),
        ('test-jet-coverage.py',
         '            ("jet_secp_scalar_add_local.v", "scalar_add_literal_local_spec", "simplicity_scalar_add"),\n',
         '            ("jet_secp_scalar_add_local.v", "scalar_add_literal_local_spec", "simplicity_scalar_add"),\n'
         '            ("jet_secp_scalar_multiply_local.v", "scalar_multiply_literal_local_spec", "simplicity_scalar_multiply"),\n')]:
        content = original(name)
        if content.count(old) != 1:
            raise ValueError('metadata replacement not unique: ' + name)
        replacements[name] = content.replace(old, new)
    hook = 'python3 scalar-add-review/test-add-public.py "${JET_C_REPO:-..}" C .\n'
    content = original('check-jets.sh')
    if content.count(hook) != 1:
        raise ValueError('multiply gate hook not unique')
    replacements['check-jets.sh'] = content.replace(hook, hook +
        'python3 scalar-multiply-review/check-multiply-public.py --repo "${JET_C_REPO:-..}" --coq .\n'
        'python3 scalar-multiply-review/test-multiply-public.py "${JET_C_REPO:-..}" .\n')
    # The new internal u128 helper has seven short definition names already
    # used by inherited core-jet proofs. Load it without opening its namespace:
    # all Check/Print commands are qualified, and inherited print context stays
    # intact. This changes formatting exposure, not the proof or checked scope.
    content = original('audit-jet-contracts.sh')
    old = "awk '/^Simplicity\\./ {print \"Require \" $0 \".\"; next}\n"
    new = old + "         /^C\\.jet_secp_umul128_exec$/ {print \"Require \" $0 \".\"; next}\n"
    if content.count(old) != 1:
        raise ValueError('contract loader adaptation not unique')
    replacements['audit-jet-contracts.sh'] = content.replace(old, new)
    patch = ['*** Begin Patch']
    for name, content in additions.items():
        patch.append('*** Add File: ' + str(target / name))
        patch += ['+' + line for line in content.splitlines()]
    for name, content in replacements.items():
        patch.append('*** Update File: ' + str(target / name))
        diff = list(difflib.unified_diff(originals[name].splitlines(), content.splitlines(), n=3))[2:]
        patch += ['@@' if line.startswith('@@') else line for line in diff]
    patch.append('*** End Patch')
    if not verify:
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    for path in source.rglob('*.v'):
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited source changed during preparation')
    for name in ['jet_contracts.expected', 'jet_assumptions.expected', 'jet_coqchk_axioms.expected']:
        if not verify and (source / 'C' / name).read_bytes() != (target / 'C' / name).read_bytes():
            raise ValueError('snapshot changed during assembly')
    for name, content in {**additions, **replacements}.items():
        if (target / name).read_bytes() != content.encode():
            raise ValueError('materialized source/metadata mismatch: ' + name)
    return {**{k: v for k, v in planned.items() if k != 'modules'}, 'candidate': str(candidate),
            'modules': [{k: v for k, v in entry.items() if k != 'text'} for entry in entries],
            'new_modules': len(entries), 'new_results': len(results), 'new_definitions': len(definitions),
            'new_provisional_coverage_entries': 1, 'snapshots_unchanged': True,
            'added_file_hashes': {name: digest(content.encode()) for name, content in additions.items()},
            'metadata': {name: {'baseline_sha256': digest(originals[name].encode()),
                               'candidate_sha256': digest(content.encode())}
                         for name, content in replacements.items()}}


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--baseline', type=Path, required=True)
    cli.add_argument('--candidate', type=Path)
    cli.add_argument('--verify', action='store_true')
    args = cli.parse_args()
    result = assemble(args.baseline, args.candidate, args.verify) if args.candidate else plan(args.baseline)
    result['modules'] = [{k: v for k, v in entry.items() if k != 'text'} for entry in result['modules']]
    print(json.dumps(result, indent=2))
