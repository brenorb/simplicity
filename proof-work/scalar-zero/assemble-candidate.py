"""Guarded scalar-zero assembly: immutable baseline and apply_patch-only edits.

The candidate's coverage entry is provisional until normal full acceptance.
Transport only the checked dependency closure; compatibility wrappers resolve
to existing C modules rather than overwriting them with self-importing aliases.
"""
import argparse
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
ARCHIVE = Path(__file__).resolve().parent
ALIASES = {'jet_secp_zero_numeric', 'jet_secp_local_regions'}
ROOTS = ['jet_secp_scalar_zero_local', 'jet_secp_scalar_canonical_parametric']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def provenance(work):
    entries = {}
    for directory in ['scalar-next', 'scalar-reduce', 'scalar-set', 'scalar-reader',
                      'scalar-reader-lifecycle', 'scalar-reader-zero', 'scalar-public-entry', 'scalar-zero']:
        archive = ARCHIVE.parent / directory
        manifest = json.loads((archive / 'manifest.json').read_text())
        for entry in manifest.get('modules', [manifest] if 'file' in manifest else []):
            name = entry['file'][:-2]
            path = archive / entry.get('path', entry.get('source', entry['file'] + '.source'))
            content = path.read_bytes()
            pinned_hash = entry.get('sha256', entry.get('source_sha256'))
            if digest(content) != pinned_hash or (work / entry['file']).read_bytes() != content:
                raise ValueError('archived/compiled source drift: ' + name)
            if name in entries:
                raise ValueError('duplicate archived module: ' + name)
            entries[name] = {'archive': str(path.resolve()), 'sha256': pinned_hash,
                             'results': entry['results'], 'text': content.decode()}
    for name in ALIASES:
        path = ARCHIVE.parent / 'scalar-next' / (name + '.v.source')
        content = path.read_bytes()
        if content != (work / (name + '.v')).read_bytes():
            raise ValueError('compatibility wrapper drift')
        expected = 'Require Export C.' + name + '.'
        if expected not in content.decode():
            raise ValueError('compatibility wrapper changed')
    return entries


def plan(base, work):
    base, work = base.resolve(), work.resolve()
    receipt = json.loads((ARCHIVE.parent / 'ge-negate/ACCEPTANCE.json').read_text())
    if base != Path(receipt['candidate']).resolve() or receipt['exit_code'] != 0:
        raise ValueError('baseline lacks reviewed terminal acceptance')
    # The same source fingerprint as the successful acceptance, including all
    # inherited production C/Haskell inputs and reviewed snapshots.
    import importlib.util
    spec = importlib.util.spec_from_file_location('audit_inputs', base / 'Coq/jet-audit-inputs.py')
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    actual = audit.fingerprint(base / 'Coq', ARCHIVE.parent.parent)
    if actual != receipt['audit_input_sha256']:
        raise ValueError('accepted baseline fingerprint changed')
    entries, order, visiting, visited = provenance(work), [], set(), set()

    def visit(name):
        if name in visited or name in ALIASES:
            return
        if name in visiting or name not in entries:
            raise ValueError('cycle or unarchived dependency: ' + name)
        visiting.add(name)
        entry = entries[name]
        for dependency in sorted(set(re.findall(r'\bOriginalC\.(\w+)', entry['text']))):
            visit(dependency)
        if (base / 'Coq/C' / (name + '.v')).exists():
            raise ValueError('new module collides with inherited source: ' + name)
        names = re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', entry['text'], re.M)
        if names != entry['results']:
            raise ValueError('result inventory drift: ' + name)
        transformed = entry['text'].replace('OriginalC.', 'C.')
        for dependency in set(re.findall(r'\bC\.(\w+)', transformed)):
            if dependency not in entries and not (base / 'Coq/C' / (dependency + '.v')).is_file():
                raise ValueError('missing inherited dependency: ' + dependency)
        definitions = re.findall(r'^(?:Local )?(?:Definition|Fixpoint)\s+(\w+)', transformed, re.M)
        order.append({'name': name, 'archive': entry['archive'], 'original_sha256': entry['sha256'],
                      'candidate_sha256': digest(transformed.encode()), 'results': names,
                      'definitions': definitions, 'text': transformed})
        visiting.remove(name)
        visited.add(name)

    for name in ROOTS:
        visit(name)
    return {'baseline': str(base), 'work': str(work), 'baseline_acceptance_session': receipt['session'],
            'baseline_fingerprint': actual, 'modules': order,
            'aliases_reused_without_overwrite': sorted(ALIASES), 'full_acceptance': False}


def assemble(base, work, candidate, verify=False):
    planned = plan(base, work)
    candidate = candidate.resolve()
    if not str(candidate).startswith('/private/tmp/') or candidate == base.resolve():
        raise ValueError('candidate must be a separate temporary directory')
    source, target = base.resolve() / 'Coq', candidate / 'Coq'
    inherited = sorted(source.rglob('*.v'))
    for path in inherited:
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited candidate source changed')
    additions = {'C/' + e['name'] + '.v': e['text'] for e in planned['modules']}
    for name in additions:
        if not verify and (target / name).exists():
            raise ValueError('candidate already assembled')
    # Standalone source gates live inside the candidate and are fingerprinted
    # by check-jets. The recursive predicate gate is inherited unchanged.
    ports = (ARCHIVE.parent / 'scalar-reader-zero/check-literal.py').read_text()
    public = (ARCHIVE / 'check-literal.py').read_text().replace(
        "archive.parent / 'scalar-reader-zero/check-literal.py'", "archive / 'check-scalar-ports.py'")
    fixtures = (ARCHIVE / 'test-literal.py').read_text()
    recursive_fixtures = (ARCHIVE.parent / 'scalar-reader-zero/test-literal.py').read_text().replace(
        "archive/'check-literal.py'", "archive/'check-scalar-ports.py'")
    additions.update({'scalar-review/check-scalar-ports.py': ports,
                      'scalar-review/check-literal.py': public,
                      'scalar-review/test-literal.py': fixtures,
                      'scalar-review/test-scalar-ports.py': recursive_fixtures})
    originals, replacements = {}, {}

    def original(name):
        content = (source / name).read_text()
        if not verify and content != (target / name).read_text():
            raise ValueError('candidate metadata differs before assembly: ' + name)
        originals[name] = content
        return content

    def extend(name, rows):
        content = original(name)
        existing = {line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')}
        if not rows or len(set(rows)) != len(rows) or existing & set(rows) or not content.endswith('\n'):
            raise ValueError('invalid inventory extension: ' + name)
        replacements[name] = content + '\n'.join(rows) + '\n'

    modules = planned['modules']
    paths = ['C/' + entry['name'] + '.v' for entry in modules]
    results = ['C.' + entry['name'] + ' ' + result for entry in modules for result in entry['results']]
    definitions = ['C.' + entry['name'] + ' ' + definition for entry in modules for definition in entry['definitions']]
    extend('_CoqProject', paths)
    extend('_CoqProject.jets', paths)
    extend('C/jet_public_theorems.txt', results)
    extend('C/jet_contract_definitions.txt', definitions)
    extend('C/jet_coverage.tsv', ['simplicity_scalar_is_zero\tC.jet_secp_scalar_zero_local\tscalar_zero_local_spec'])

    def replace_once(name, old, new):
        content = original(name)
        if content.count(old) != 1:
            raise ValueError('metadata replacement not unique: ' + name)
        replacements[name] = content.replace(old, new)

    replace_once('jet-coverage.py', '"simplicity_ge_negate"}:',
                 '"simplicity_ge_negate", "simplicity_scalar_is_zero"}:')
    row = '            ("jet_secp_ge_negate_local.v", "ge_negate_literal_local_spec", "simplicity_ge_negate"),\n'
    replace_once('test-jet-coverage.py', row, row +
                 '            ("jet_secp_scalar_zero_local.v", "scalar_zero_local_spec", "simplicity_scalar_is_zero"),\n')
    hook = 'python3 ge-negate-review/test-ge-negate-wiring.py --repo "${JET_C_REPO:-..}" --candidates C --dependencies C\n'
    gates = ('python3 scalar-review/check-literal.py --repo "${JET_C_REPO:-..}" --source C --coq .\n'
             'python3 scalar-review/test-literal.py "${JET_C_REPO:-..}" C .\n'
             'python3 scalar-review/test-scalar-ports.py "${JET_C_REPO:-..}" C .\n')
    replace_once('check-jets.sh', hook, hook + gates)
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
            raise ValueError('inherited snapshot changed during assembly')
    for name, content in additions.items():
        if (target / name).read_bytes() != content.encode():
            raise ValueError('materialized source mismatch: ' + name)
    for name, content in replacements.items():
        if (target / name).read_bytes() != content.encode():
            raise ValueError('candidate infrastructure mismatch: ' + name)
    expected_sources = {p.relative_to(source) for p in inherited} | {Path(p) for p in paths}
    if {p.relative_to(target) for p in target.rglob('*.v')} != expected_sources:
        raise ValueError('missing/unregistered candidate source')
    return {**{k: v for k, v in planned.items() if k != 'modules'}, 'candidate': str(candidate),
            'modules': [{k: v for k, v in e.items() if k != 'text'} for e in modules],
            'inherited_all_v_sources_byte_identical': len(inherited),
            'new_results': len(results), 'new_definitions': len(definitions),
            'new_provisional_coverage_entries': 1, 'snapshots_unchanged': True,
            'added_file_hashes': {name: digest(content.encode()) for name, content in additions.items()},
            'metadata': {name: {'baseline_sha256': digest(originals[name].encode()),
                                'candidate_sha256': digest(content.encode())}
                         for name, content in replacements.items()}}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    parser.add_argument('--candidate', type=Path)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    if args.candidate is None:
        result = plan(args.baseline, args.work)
        result['modules'] = [{k: v for k, v in e.items() if k != 'text'} for e in result['modules']]
    else:
        result = assemble(args.baseline, args.work, args.candidate, args.verify)
    print(json.dumps(result, indent=2))
