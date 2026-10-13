"""Namespace-only lambda closure promotion; no snapshots or main writes."""
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
PREFIXES = ('BorrowC.', 'BorrowFC.', 'LambdaC.', 'LamSpecC.', 'ReadonlyC.',
            'LamCallC.', 'LamInitC.', 'LamFrameC.')
ROOT = 'jet_secp_scalar_lambda_local'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def transport(text):
    for prefix in PREFIXES:
        text = text.replace(prefix, 'C.')
    return text


def plan(base):
    base = base.resolve()
    parent = ARCHIVE.parent / 'scalar-square-integration'
    accepted = json.loads((parent / 'ACCEPTANCE.json').read_text())
    if base != Path(accepted['candidate']).resolve() or accepted['exit_code'] != 0:
        raise ValueError('baseline is not the terminal accepted multiply candidate')
    if digest(Path(accepted['log']).read_bytes()) != accepted['log_sha256']:
        raise ValueError('parent acceptance log changed')
    load('square_normal_parent', parent / 'review-normal.py').review(parent / 'ASSEMBLY.json')
    load('lambda_frames_proof', ARCHIVE.parent / 'scalar-lambda-frames/review.py').review()
    audit = load('square_base_inputs', base / 'Coq/jet-audit-inputs.py')
    fingerprint = audit.fingerprint(base / 'Coq', REPO)
    if fingerprint != accepted['audit_input_sha256']:
        raise ValueError('accepted baseline input drift')
    entries = {}
    for family in ['scalar-mul-borrowed', 'scalar-mul-borrowed-function', 'scalar-lambda',
                   'scalar-lambda-caller', 'scalar-lambda-startup', 'scalar-lambda-frames']:
        directory = ARCHIVE.parent / family
        manifest = json.loads((directory / 'manifest.json').read_text())
        for entry in manifest['modules']:
            path = directory / (entry['file'] + '.source'); raw = path.read_bytes()
            if digest(raw) != entry['sha256'] or entry['module'] in entries:
                raise ValueError('archived source drift/duplicate')
            entries[entry['module']] = {**entry, 'name': entry['file'][:-2],
                'original_module': entry['module'], 'archive': str(path.resolve()),
                'original_sha256': entry['sha256'], 'family': family, 'text': raw.decode()}
    visited, active, order, inherited = set(), set(), [], {}

    def visit(key):
        _, name = key.split('.', 1)
        path = base / 'Coq/C' / (name + '.v')
        if path.exists():
            if key in entries and transport(entries[key]['text']).encode() != path.read_bytes():
                raise ValueError('new/inherited module collision: ' + key)
            inherited[name] = digest(path.read_bytes()); return
        if key in visited:
            return
        if key not in entries or key in active:
            raise ValueError('missing/cyclic square dependency: ' + key)
        active.add(key); entry = entries[key]
        for ns, dep in sorted(set(re.findall(r'\b(BorrowC|BorrowFC|LambdaC|LamSpecC|ReadonlyC|LamCallC|LamInitC|LamFrameC|C)\.(\w+)', entry['text']))):
            visit(ns + '.' + dep)
        if (re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', entry['text'], re.M) != entry['results']
                or re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', entry['text'], re.M) != entry['definitions']):
            raise ValueError('declaration inventory drift')
        if any(e['name'] == name for e in order):
            raise ValueError('normal module name collision')
        text = transport(entry['text'])
        order.append({**entry, 'text': text, 'candidate_sha256': digest(text.encode())})
        active.remove(key); visited.add(key)

    visit('LamFrameC.jet_secp_scalar_lambda_fresh')
    visit('LamFrameC.' + ROOT)
    return {'baseline': str(base), 'baseline_fingerprint': fingerprint,
            'modules': order, 'inherited_dependency_hashes': inherited,
            'excluded_unselected_modules': sorted(set(entries) - visited),
            'full_acceptance': False, 'checkout_coverage_added': 0}


def assemble(base, candidate, verify=False):
    planned = plan(base); base, candidate = base.resolve(), candidate.resolve()
    if not str(candidate).startswith('/private/tmp/') or candidate == base:
        raise ValueError('candidate must be separate and temporary')
    source, target = base / 'Coq', candidate / 'Coq'
    for name in ['C', 'Haskell']:
        if not (candidate / name).is_symlink() or (candidate / name).resolve() != (REPO / name).resolve():
            raise ValueError('candidate lacks verified production-source layout')
    for path in source.rglob('*.v'):
        if path.read_bytes() != (target / path.relative_to(source)).read_bytes():
            raise ValueError('inherited candidate source changed')
    entries = planned['modules']
    additions = {'C/' + entry['name'] + '.v': entry['text'] for entry in entries}
    for name in ['check-lambda-public.py', 'test-lambda-public.py']:
        additions['scalar-lambda-review/' + name] = (ARCHIVE / name).read_text()
    if not verify and any((target / name).exists() for name in additions):
        raise ValueError('candidate already assembled')
    originals, replacements = {}, {}

    def original(name):
        content = (source / name).read_text()
        if not verify and (target / name).read_text() != content:
            raise ValueError('candidate metadata changed before assembly')
        originals[name] = content; return content

    def extend(name, rows):
        content = original(name)
        old = {line.strip() for line in content.splitlines() if line.strip() and not line.startswith('#')}
        if old & set(rows) or len(rows) != len(set(rows)) or not content.endswith('\n'):
            raise ValueError('invalid inventory extension')
        replacements[name] = content + '\n'.join(rows) + '\n'

    paths = ['C/' + entry['name'] + '.v' for entry in entries]
    results = ['C.' + entry['name'] + ' ' + n for entry in entries for n in entry['results']]
    definitions = ['C.' + entry['name'] + ' ' + n for entry in entries for n in entry['definitions']]
    for name in ['_CoqProject', '_CoqProject.jets']:
        extend(name, paths)
    extend('C/jet_public_theorems.txt', results); extend('C/jet_contract_definitions.txt', definitions)
    extend('C/jet_coverage.tsv', ['simplicity_scalar_multiply_lambda\tC.' + ROOT + '\tscalar_lambda_initialized_local_spec'])
    old_contract = '                contract = rf"\\bsecp_jet_local_spec\\s+f_{re.escape(name)}\\b"\n'
    new_contract = old_contract + (
        '            elif name == "simplicity_scalar_multiply_lambda":\n'
        '                # Only this reviewed initialized-memory contract is counted.\n'
        '                contract = (r"\\bsecp_jet_initialized_local_spec\\s+scalar_lambda_initialized\\s+"\n'
        '                            r"f_simplicity_scalar_multiply_lambda\\b")\n')
    coverage_tests = r'''        # Lambda requires its exact initialized-memory contract.
        lam = project / "C/jet_secp_scalar_lambda_local.v"
        lam_original = lam.read_text()
        declaration = "Theorem scalar_lambda_initialized_local_spec :"
        for old, new in (
            ("secp_jet_initialized_local_spec scalar_lambda_initialized", "secp_jet_initialized_local_spec True"),
            ("secp_jet_initialized_local_spec scalar_lambda_initialized", "secp_jet_local_spec"),
            ("f_simplicity_scalar_multiply_lambda", "f_simplicity_scalar_square"),
            (declaration, declaration + " False ->"),
        ):
            start = lam_original.index(declaration)
            lam.write_text(lam_original[:start] + lam_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        lam.write_text(lam_original)
        assert coverage.inventory() == rows
'''
    printer_anchor = '         /^C\\.jet_secp_umul128_exec$/ {print "Require " $0 "."; next}\n'
    printer_names = '|'.join(re.escape(e['name']) for e in entries)
    # Load new modules without opening short names in inherited contract output.
    printer_extension = '         /^C\\.(' + printer_names + ')$/ {print "Require " $0 "."; next}\n'
    for name, old, new in [
        ('jet-coverage.py', old_contract, new_contract),
        ('test-jet-coverage.py',
         '        # This positive fixture checks bookkeeping only. The actual application\n',
         coverage_tests + '        # This positive fixture checks bookkeeping only. The actual application\n'),
        ('audit-jet-contracts.sh', printer_anchor, printer_anchor + printer_extension),
        ('check-jets.sh', 'python3 scalar-square-review/test-square-public.py "${JET_C_REPO:-..}" .\n',
         'python3 scalar-square-review/test-square-public.py "${JET_C_REPO:-..}" .\n'
         'python3 scalar-lambda-review/check-lambda-public.py --repo "${JET_C_REPO:-..}" --coq .\n'
         'python3 scalar-lambda-review/test-lambda-public.py "${JET_C_REPO:-..}" .\n')]:
        content = original(name)
        if content.count(old) != 1:
            raise ValueError('nonunique gate adaptation: ' + name)
        replacements[name] = content.replace(old, new)
    patch = ['*** Begin Patch']
    for name, content in additions.items():
        patch += ['*** Add File: ' + str(target / name)] + ['+' + line for line in content.splitlines()]
    for name, content in replacements.items():
        patch.append('*** Update File: ' + str(target / name))
        diff = list(difflib.unified_diff(originals[name].splitlines(), content.splitlines(), n=3))[2:]
        patch += ['@@' if line.startswith('@@') else line for line in diff]
    patch.append('*** End Patch')
    if not verify:
        subprocess.run(['apply_patch'], input='\n'.join(patch) + '\n', text=True, check=True,
                       stdout=subprocess.DEVNULL)
    for name, content in {**additions, **replacements}.items():
        if (target / name).read_bytes() != content.encode():
            raise ValueError('materialized source/gate mismatch')
    for name in ['jet_contracts.expected', 'jet_assumptions.expected', 'jet_coqchk_axioms.expected']:
        if not verify and (source / 'C' / name).read_bytes() != (target / 'C' / name).read_bytes():
            raise ValueError('snapshot changed during assembly')
    return {**{key: value for key, value in planned.items() if key != 'modules'},
            'candidate': str(candidate), 'modules': [{key: value for key, value in e.items() if key != 'text'} for e in entries],
            'new_modules': len(entries), 'new_results': len(results), 'new_definitions': len(definitions),
            'new_provisional_coverage_entries': 1, 'full_acceptance': False,
            'added_file_hashes': {name: digest(content.encode()) for name, content in additions.items()},
            'metadata': {name: {'baseline_sha256': digest(originals[name].encode()),
                               'candidate_sha256': digest(content.encode())} for name, content in replacements.items()}}


if __name__ == '__main__':
    cli = argparse.ArgumentParser(); cli.add_argument('--baseline', type=Path, required=True)
    cli.add_argument('--candidate', type=Path); cli.add_argument('--verify', action='store_true'); args = cli.parse_args()
    result = assemble(args.baseline, args.candidate, args.verify) if args.candidate else plan(args.baseline)
    result['modules'] = [{key: value for key, value in e.items() if key != 'text'} for e in result['modules']]
    print(json.dumps(result, indent=2))

