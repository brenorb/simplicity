"""Exact scalar-normalize/negate closure transport, never proof acceptance.

Preparation may run over the frozen, snapshot-reviewed scalar-zero candidate
while its full acceptance is running. Nothing in that baseline is written.
Normal compile/type/dependency checks and terminal parent/full acceptance are
still required before registration. Source edits use apply_patch exclusively.
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
FAMILIES = ['scalar-next', 'scalar-writer', 'scalar-normalize', 'scalar-negate',
            'scalar-negate-canonical', 'scalar-negate-public']
ROOTS = ['jet_secp_scalar_normalize_local', 'jet_secp_scalar_negate_local',
         'jet_secp_canonical_scalar_negate_parametric']
PREFIXES = ('OriginalC.', 'WriterC.', 'NegC.')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def transport(text):
    for prefix in PREFIXES:
        text = text.replace(prefix, 'C.')
    return text


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def provenance():
    entries = {}
    for family in FAMILIES:
        directory = ARCHIVE.parent / family
        manifest = json.loads((directory / 'manifest.json').read_text())
        work = Path(manifest['scratch'])
        for entry in manifest['modules']:
            name = entry['file'][:-2]
            source = directory / entry.get('path', entry['file'] + '.source')
            raw = source.read_bytes()
            if digest(raw) != entry['sha256'] or (work / entry['file']).read_bytes() != raw:
                raise ValueError('archived/checked source drift: ' + name)
            if name in entries:
                raise ValueError('duplicate archived module: ' + name)
            entries[name] = {'name': name, 'archive': str(source.resolve()),
                             'family': family, 'scratch': str(work),
                             'original_sha256': entry['sha256'],
                             'original_module': entry.get('module', 'OriginalC.' + name),
                             'results': entry['results'], 'text': raw.decode()}
    return entries


def plan(base):
    base = base.resolve()
    zero = ARCHIVE.parent / 'scalar-zero'
    assembly = json.loads((zero / 'ASSEMBLY.json').read_text())
    reviewed = json.loads((zero / 'NORMAL-ASSUMPTION-REVIEW.json').read_text())
    if base != Path(assembly['candidate']).resolve():
        raise ValueError('baseline is not the frozen scalar-zero candidate')
    audit = load('scalar_integration_inputs', base / 'Coq/jet-audit-inputs.py')
    fingerprint = audit.fingerprint(base / 'Coq', REPO)
    if fingerprint != reviewed['candidate_preacceptance_fingerprint']:
        raise ValueError('reviewed scalar-zero baseline fingerprint changed')
    if reviewed['generation_exit_code'] != 0 or not reviewed['exact_namespace_transport_dependencies']:
        raise ValueError('baseline dependency evidence missing')
    entries, order, inherited, visited, active = provenance(), [], {}, set(), set()

    def visit(name, namespace=None):
        inherited_path = base / 'Coq/C' / (name + '.v')
        if inherited_path.is_file():
            raw = inherited_path.read_bytes()
            if name in entries and transport(entries[name]['text']).encode() != raw:
                raise ValueError('inherited source differs from checked archive: ' + name)
            if namespace == 'OriginalC' and name not in entries:
                original = Path(assembly['work']) / (name + '.v')
                text = original.read_text()
                if (transport(text).encode() != raw
                        and text.strip() != 'Require Export C.' + name + '.'):
                    raise ValueError('unreviewed inherited namespace mapping: ' + name)
            inherited[name] = digest(raw)
            return
        if name in visited:
            return
        if name in active or name not in entries:
            raise ValueError('cycle or unarchived dependency: ' + name)
        active.add(name)
        entry = entries[name]
        for prefix, dependency in sorted(set(re.findall(r'\b(OriginalC|WriterC|NegC|C)\.(\w+)', entry['text']))):
            visit(dependency, prefix)
        names = re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', entry['text'], re.M)
        if names != entry['results']:
            raise ValueError('result inventory drift: ' + name)
        text = transport(entry['text'])
        definitions = re.findall(r'^(?:Local )?(?:Definition|Fixpoint)\s+(\w+)', text, re.M)
        order.append({**entry, 'text': text, 'candidate_sha256': digest(text.encode()),
                      'definitions': definitions})
        active.remove(name)
        visited.add(name)

    for name in ROOTS:
        visit(name)
    if len(order) != 25 or sum(len(e['results']) for e in order) != 96:
        raise ValueError('unexpected checked dependency closure')
    return {'baseline': str(base), 'baseline_fingerprint': fingerprint,
            'baseline_full_acceptance_required': True, 'modules': order,
            'inherited_dependency_hashes': inherited,
            'excluded_unselected_new_modules': sorted(n for n in entries if n not in visited
                and not (base / 'Coq/C' / (n + '.v')).exists()),
            'full_acceptance': False, 'checkout_coverage_added': 0}


def assemble(base, candidate, verify=False):
    planned = plan(base)
    candidate = candidate.resolve()
    if not str(candidate).startswith('/private/tmp/') or candidate == base.resolve():
        raise ValueError('candidate must be a separate temporary directory')
    source, target = base.resolve() / 'Coq', candidate / 'Coq'
    inherited = sorted(source.rglob('*.v'))
    for path in inherited:
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited candidate source changed')
    additions = {'C/' + e['name'] + '.v': e['text'] for e in planned['modules']}
    if not verify and any((target / name).exists() for name in additions):
        raise ValueError('candidate already assembled')
    # Reuse previously tested gates; rewrite only their explicit archive paths.
    gates = {
        'check-negate-ports.py': ('scalar-negate-canonical', 'check-literal.py', {
            "archive.parent / 'scalar-reader-zero/check-literal.py'": "coq / 'scalar-review/check-scalar-ports.py'"}),
        'check-negate-public.py': ('scalar-negate-public', 'check-literal.py', {
            "archive.parent / 'scalar-negate-canonical/check-literal.py'": "archive / 'check-negate-ports.py'"}),
        'check-normalize-public.py': ('scalar-normalize', 'check-literal.py', {
            "archive.parent / 'scalar-reader-zero/check-literal.py'": "coq / 'scalar-review/check-scalar-ports.py'"}),
        'test-negate-ports.py': ('scalar-negate-canonical', 'test-literal.py', {
            "with_name('check-literal.py')": "with_name('check-negate-ports.py')"}),
        'test-negate-public.py': ('scalar-negate-public', 'test-literal.py', {
            "with_name('check-literal.py')": "with_name('check-negate-public.py')"}),
        'test-normalize-public.py': ('scalar-normalize', 'test-literal.py', {
            "with_name('check-literal.py')": "with_name('check-normalize-public.py')"}),
    }
    for name, (family, filename, rewrites) in gates.items():
        text = (ARCHIVE.parent / family / filename).read_text()
        for old, new in rewrites.items():
            if text.count(old) != 1:
                raise ValueError('gate relocation not unique')
            text = text.replace(old, new)
        additions['scalar-integration-review/' + name] = text
    originals, replacements = {}, {}

    def original(name):
        content = (source / name).read_text()
        if not verify and content != (target / name).read_text():
            raise ValueError('candidate metadata changed before assembly: ' + name)
        originals[name] = content
        return content

    def extend(name, rows):
        content = original(name)
        existing = {line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')}
        if len(set(rows)) != len(rows) or existing & set(rows) or not content.endswith('\n'):
            raise ValueError('invalid inventory extension: ' + name)
        replacements[name] = content + '\n'.join(rows) + '\n'

    modules = planned['modules']
    paths = ['C/' + e['name'] + '.v' for e in modules]
    results = ['C.' + e['name'] + ' ' + n for e in modules for n in e['results']]
    definitions = ['C.' + e['name'] + ' ' + n for e in modules for n in e['definitions']]
    extend('_CoqProject', paths)
    extend('_CoqProject.jets', paths)
    extend('C/jet_public_theorems.txt', results)
    extend('C/jet_contract_definitions.txt', definitions)
    extend('C/jet_coverage.tsv', [
        'simplicity_scalar_normalize\tC.jet_secp_scalar_normalize_local\tscalar_normalize_local_spec',
        'simplicity_scalar_negate\tC.jet_secp_scalar_negate_local\tscalar_negate_local_spec'])

    def replace_once(name, old, new):
        content = original(name)
        if content.count(old) != 1:
            raise ValueError('metadata replacement not unique: ' + name)
        replacements[name] = content.replace(old, new)

    replace_once('jet-coverage.py', '"simplicity_scalar_is_zero"}:',
        '"simplicity_scalar_is_zero", "simplicity_scalar_normalize", "simplicity_scalar_negate"}:')
    row = '            ("jet_secp_scalar_zero_local.v", "scalar_zero_local_spec", "simplicity_scalar_is_zero"),\n'
    replace_once('test-jet-coverage.py', row, row +
        '            ("jet_secp_scalar_normalize_local.v", "scalar_normalize_local_spec", "simplicity_scalar_normalize"),\n'
        '            ("jet_secp_scalar_negate_local.v", "scalar_negate_local_spec", "simplicity_scalar_negate"),\n')
    hook = 'python3 scalar-review/test-scalar-ports.py "${JET_C_REPO:-..}" C .\n'
    commands = ''
    for name in ['normalize-public', 'negate-ports', 'negate-public']:
        commands += ('python3 scalar-integration-review/check-' + name + '.py'
                     ' --repo "${JET_C_REPO:-..}" --source C --dependencies C --coq .\n'
                     'python3 scalar-integration-review/test-' + name + '.py "${JET_C_REPO:-..}" C C .\n')
    replace_once('check-jets.sh', hook, hook + commands)
    patch = ['*** Begin Patch']
    for name, content in additions.items():
        patch.append('*** Add File: ' + str(target / name))
        patch.extend('+' + line for line in content.splitlines())
    for name, content in replacements.items():
        patch.append('*** Update File: ' + str(target / name))
        diff = list(difflib.unified_diff(originals[name].splitlines(), content.splitlines(), n=3))[2:]
        patch.extend('@@' if line.startswith('@@') else line for line in diff)
    patch.append('*** End Patch')
    if not verify:
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    for path in inherited:
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited source changed after assembly')
    for name in ['C/jet_contracts.expected', 'C/jet_assumptions.expected', 'C/jet_coqchk_axioms.expected']:
        if (source / name).read_bytes() != (target / name).read_bytes():
            raise ValueError('inherited snapshot changed during preparation')
    for name, content in {**additions, **replacements}.items():
        if (target / name).read_bytes() != content.encode():
            raise ValueError('materialized source/infrastructure mismatch: ' + name)
    expected_sources = {p.relative_to(source) for p in inherited} | {Path(p) for p in paths}
    if {p.relative_to(target) for p in target.rglob('*.v')} != expected_sources:
        raise ValueError('missing/unregistered candidate source')
    return {**{k: v for k, v in planned.items() if k != 'modules'}, 'candidate': str(candidate),
            'modules': [{k: v for k, v in e.items() if k != 'text'} for e in modules],
            'inherited_all_v_sources_byte_identical': len(inherited),
            'new_results': len(results), 'new_definitions': len(definitions),
            'new_provisional_coverage_entries': 2, 'snapshots_unchanged': True,
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
    if args.candidate is None:
        result = plan(args.baseline)
        result['modules'] = [{k: v for k, v in e.items() if k != 'text'} for e in result['modules']]
    else:
        result = assemble(args.baseline, args.candidate, args.verify)
    print(json.dumps(result, indent=2))
