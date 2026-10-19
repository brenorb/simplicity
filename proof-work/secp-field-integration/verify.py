"""Fresh reports and recursive kernel check of the regular-name candidate.

This does not accept shared coverage. The exact 413 inherited theorem profiles
are compared after the reversible module rename, not replaced by a broad union
allowlist. Launch records are never treated as completed verification.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('field_integration_assembly', HERE / 'assemble.py')
a = importlib.util.module_from_spec(sp)
sp.loader.exec_module(a)
s = a.s
g = s.load('field_integration_reports', HERE.parent / 'elements-tap-getters/check.py')


def built():
    work, r = a.identity()
    b = json.loads((HERE / 'BUILT.json').read_text())
    if not b['complete'] or b['preparation_sha256'] != s.sha((HERE / 'PREPARATION.json').read_bytes()):
        raise ValueError('regular build not completed for these inputs')
    for name, row in b['commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('regular build command/log changed')
    for name, digest in b['source_objects'].items():
        if s.sha((work / name).with_suffix('.vo').read_bytes()) != digest:
            raise ValueError('regular built object changed: ' + name)
    return work, r, b


def inherited_profiles(mapping):
    names = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', a.SOURCE_REV,
        'proof-work'], cwd=a.REPO, text=True).splitlines()
    profiles, inputs = {}, {}
    for name in names:
        if not name.endswith(('/CHECKED.json', '/RUN.json')):
            continue
        raw = a.blob(name)
        record = json.loads(raw)
        used = False
        for theorem, axioms in record.get('dependencies', {}).items():
            module, short = theorem.rsplit('.', 1)
            if module not in mapping:
                continue
            new = mapping[module] + '.' + short
            if new in profiles and profiles[new] != set(axioms):
                raise ValueError('inconsistent recorded profile: ' + theorem)
            profiles[new] = set(axioms)
            used = True
        if used:
            inputs[name] = s.sha(raw)
    return profiles, inputs


def source_reviews(work):
    archive_path = 'proof-work/secp-field-literal/ARCHIVED-INPUTS.json'
    archives = json.loads(a.blob(archive_path))['inputs']
    gates, view, changes, inputs = work / 'review-gates', work / 'review-candidates', {}, {}
    for original, row in archives.items():
        if not original.startswith('Coq/negate-review/'):
            continue
        name = 'proof-work/secp-field-literal/' + row['archive']
        raw = a.blob(name)
        if s.sha(raw) != row['sha256']:
            raise ValueError('archived gate hash differs: ' + name)
        changes[gates / Path(original).name] = raw.decode()
        inputs[name] = s.sha(raw)
        if original.endswith('.json'):
            changes[view / Path(original).name] = raw.decode()
    for name in ['jet_secp_canonical_negate', 'jet_secp_negate_local', 'jet_literal_division_add',
                 'jet_canonical_add_adapter', 'jet_secp_negate_literal_contract', 'jet_haskell_word_conversion']:
        changes[view / (name + '.v')] = (work / 'Coq/C' / (name + '.v')).read_text()
    s.changed(changes)
    commands = {'multiply-source': [sys.executable, '-B', str(HERE / 'review.py')]}
    for family in ['negate-wiring', 'recursive-ports', 'literal-ports', 'foundations']:
        for action in ['check', 'test']:
            name = action + '-' + family
            commands[name] = [sys.executable, '-B', str(gates / (name + '.py')),
                '--repo', str(work), '--candidates', str(view)]
    for action in ['check', 'test']:
        name = action + '-normalize'
        commands[name] = [sys.executable, '-B', str(work / 'Coq' / (action + '-secp-normalize-specification.py'))]
    rows = {}
    for name, command in commands.items():
        rows[name] = s.run(work, command, 'integration-review-' + name, 180)
        print('Passed integration source review: ' + name, flush=True)
    return rows, inputs


def full_reports(work, modules, commands):
    # Same complete queries/parser as the packet reporter, with a measured
    # whole-closure deadline. The old 180-second per-packet deadline terminated
    # after 329 of these 413 declarations, not after a proof failure.
    results, definitions = [], []
    for module, path in modules:
        rs, ds = g.declarations(path.read_text(), module)
        results += rs
        definitions += ds
    header = ['Require ' + ' '.join(m for m, _ in modules) + '.']
    axioms = header[:]
    contracts = header + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    for n in results:
        axioms += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    for kind, names in [('TYPE', results), ('DEF', definitions)]:
        for n in names:
            contracts += ['Goal True. idtac "TAP_' + kind + ' ' + n + '". exact I. Qed.',
                ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
    for stem, query in [('integration-assumptions', axioms), ('integration-contracts', contracts)]:
        path = work / (stem.replace('-', '_') + '.v')
        s.changed({path: '\n'.join(query) + '\n'})
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', str(path)], stem, 600)
    deps = s.reports.assumptions((work / 'integration-assumptions.log').read_text())
    if set(deps) != set(results) or any(not ds <= s.SIX for ds in deps.values()):
        raise ValueError('missing declaration or unreviewed assumption in full report')
    text = (work / 'integration-contracts.log').read_text()
    if ('...' in text or re.search(r'\?[A-Za-z]', text) or
            re.findall(r'(?m)^TAP_(TYPE|DEF) (\S+)$', text) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
        raise ValueError('incomplete full theorem types/definitions')
    return results, definitions, deps


def reports():
    work, r, b = built()
    launch = HERE / 'REPORT-LAUNCH.json'
    if (HERE / 'REPORT-LAUNCH.json').exists():
        failure = json.loads((HERE / 'REPORT-TIMEOUT.json').read_text())
        old_verifier = subprocess.check_output(['git', 'show',
            failure['failed_verifier_commit'] + ':proof-work/secp-field-integration/verify.py'], cwd=a.REPO)
        if (not failure['terminal'] or failure['complete'] or failure['deadline_seconds'] != 180 or
                failure['launch_sha256'] != s.sha(launch.read_bytes()) or
                failure['failed_verifier_sha256'] != s.sha(old_verifier) or
                failure['failed_log_sha256'] != s.sha((HERE / 'report-timeout-assumptions.log').read_bytes())):
            raise ValueError('old report is not a recorded terminal timeout')
        launch = HERE / 'REPORT-RETRY-LAUNCH.json'
        if launch.exists():
            raise ValueError('bounded report retry already launched; poll original handle')
    expected, inherited = inherited_profiles(r['module_renaming'])
    modules = [(new, work / 'Coq' / (new.replace('.', '/') + '.v'))
        for new in r['module_renaming'].values()]
    declarations = {n for module, path in modules for n in g.declarations(path.read_text(), module)[0]}
    if set(expected) != declarations or len(declarations) != 413:
        raise ValueError('missing inherited exact assumption profiles')
    s.changed({launch: json.dumps(dict(candidate=str(work), complete=False, deadline_seconds=600,
        built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes())), indent=2) + '\n'})
    commands = {}
    results, definitions, dependencies = full_reports(work, modules, commands)
    if dependencies != expected:
        raise ValueError('regular-name theorem assumptions differ from checked originals')
    root = r['root'] + '.fe_multiply_literal_local_spec'
    if dependencies[root] != s.SIX:
        raise ValueError('public endpoint does not retain exactly the six inherited assumptions')
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet']
    query = subprocess.run(command, input='Require ' + r['root'] + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60)
    # Print Libraries includes nested module names; only explicit loaded-library
    # lines beginning with C. or Simplicity. belong to the local closure.
    loaded = set(re.findall(r'^\s+((?:C|Simplicity|Util)\.[\w.]+)\s*$', query.stdout, re.M))
    wanted = {n.removeprefix('Coq/').removesuffix('.v').replace('/', '.') for n in r['sources']}
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or loaded != wanted:
        raise ValueError('fresh loaded local closure differs: missing ' + str(sorted(wanted - loaded)) +
            ', added ' + str(sorted(loaded - wanted)))
    if any(old in query.stdout for old in r['module_renaming']):
        raise ValueError('private namespace leaked into the ordinary build')
    commands['original-targets'] = s.run(work, [sys.executable, '-B', 'check-jet-source-target.py'],
        'integration-original-targets', 60)
    reviews, review_inputs = source_reviews(work)
    built()
    out = dict(candidate=str(work), built_sha256=s.sha((HERE / 'BUILT.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes()), inherited_profile_inputs=inherited,
        results=results, definitions=definitions, dependencies={n: sorted(ds) for n, ds in dependencies.items()},
        commands=commands, loaded_source_modules=sorted(loaded), public_contract=root,
        source_review_commands=reviews, source_review_inputs=review_inputs,
        reviewer_sha256=s.sha((HERE / 'review.py').read_bytes()),
        multiply_gate_sha256=s.sha((HERE.parent / 'secp-field-literal/check-source.py').read_bytes()),
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'REPORTED.json': json.dumps(out, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'integration-assumptions.log': (work / 'integration-assumptions.log').read_text(),
        HERE / 'integration-contracts.log': (work / 'integration-contracts.log').read_text(),
        HERE / 'original-targets.log': (work / 'integration-original-targets.log').read_text()})
    print('Fresh ordinary-module reports: 413 exact inherited profiles; 235 loaded source-built modules', flush=True)


def reported():
    work, r, b = built()
    out = json.loads((HERE / 'REPORTED.json').read_text())
    expected, inherited = inherited_profiles(r['module_renaming'])
    if (out['built_sha256'] != s.sha((HERE / 'BUILT.json').read_bytes()) or
            out['verifier_sha256'] != s.sha(Path(__file__).read_bytes()) or
            out['reviewer_sha256'] != s.sha((HERE / 'review.py').read_bytes()) or
            out['multiply_gate_sha256'] != s.sha((HERE.parent / 'secp-field-literal/check-source.py').read_bytes()) or
            out['inherited_profile_inputs'] != inherited or
            {n: set(ds) for n, ds in out['dependencies'].items()} != expected):
        raise ValueError('reported exact inputs/profiles changed')
    for name, digest in out['source_review_inputs'].items():
        if s.sha(a.blob(name)) != digest:
            raise ValueError('source-review input changed: ' + name)
    for name, row in out['source_review_commands'].items():
        if row['exit_code'] or row['log_sha256'] != s.sha((work / ('integration-review-' + name + '.log')).read_bytes()):
            raise ValueError('source-review command/log changed: ' + name)
    for name, row in out['commands'].items():
        stem = 'integration-original-targets' if name == 'original-targets' else name
        if row['exit_code'] or row['log_sha256'] != s.sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('report command/log changed: ' + name)
    for name in ['integration-assumptions.log', 'integration-contracts.log']:
        if (HERE / name).read_bytes() != (work / name).read_bytes():
            raise ValueError('archived report changed: ' + name)
    return work, r, out


def kernel():
    work, r, out = reported()
    if (HERE / 'KERNEL-LAUNCH.json').exists():
        raise ValueError('kernel phase already launched; poll original handle')
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + r['root']]
    s.changed({HERE / 'KERNEL-LAUNCH.json': json.dumps(dict(candidate=str(work), command=command,
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes()), complete=False), indent=2) + '\n'})
    row = s.run(work, command, 'integration-kernel', 900)
    text = (work / 'integration-kernel.log').read_text()
    allowlist = (work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()
    s.kernel.kernel(text, sorted(allowlist))
    reported()
    s.changed({HERE / 'CHECKED.json': json.dumps(dict(candidate=str(work),
        reported_sha256=s.sha((HERE / 'REPORTED.json').read_bytes()), kernel=row,
        recursive_kernel_check=True, normal_registration=False, coverage_added=0), indent=2) + '\n',
        HERE / 'integration-kernel.log': text})
    print('Recursive kernel check passed for the ordinary C.* field-multiply root', flush=True)


def check():
    work, r, out = reported()
    checked = json.loads((HERE / 'CHECKED.json').read_text())
    if (not checked['recursive_kernel_check'] or checked['kernel']['exit_code'] or
            checked['reported_sha256'] != s.sha((HERE / 'REPORTED.json').read_bytes()) or
            checked['kernel']['log_sha256'] != s.sha((work / 'integration-kernel.log').read_bytes()) or
            (HERE / 'integration-kernel.log').read_bytes() != (work / 'integration-kernel.log').read_bytes()):
        raise ValueError('completed kernel evidence changed')
    s.kernel.kernel((work / 'integration-kernel.log').read_text(),
        sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    print('Exact regular build, 413 theorem profiles, sources/objects and recursive kernel evidence verified')


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'reports', 'kernel', 'check'}:
        raise SystemExit('usage: verify.py reports|kernel|check')
    {'reports': reports, 'kernel': kernel, 'check': check}[sys.argv[1]]()
