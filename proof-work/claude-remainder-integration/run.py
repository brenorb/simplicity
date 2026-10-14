"""Frozen, isolated audits of the remaining non-linked Claude support.

Sources and objects are copied, never compiler-output symlinks into main.
Each translation unit has its own C namespace. Kernel checking is recursive.
No new candidate is promoted into the normal jet registry by this command.
"""
import argparse
from functools import lru_cache
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
COMMIT = '30404face45383153528f36d915de6d7df11f3f4'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


old = load('remainder_previous', HERE.parent / 'bitcoin-composition-integration/run.py')
patcher = old.current.stage.patch
sha = old.sha
scanner = old.current.stage.scanner
reports = old.current.gate.audit.normal
kernel = old.current.gate.audit.kernel
inputs = old.current.inputs
ENV = dict(old.current.gate.audit.ENV)
SIX = old.current.ALLOWED
EIGHT = SIX | {'Events.external_functions_properties', 'Events.inline_assembly_properties'}
PATHS = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', COMMIT, 'Coq'], cwd=REPO, text=True).splitlines()
PATH_SET = set(PATHS)
C_NEW = [Path(p).stem for p in PATHS if p.startswith('Coq/C/') and p.endswith('.v')
         and not (REPO / p).exists() and Path(p).stem not in ['jets_elements_env', 'jet_frame_constructible_secp']]
GROUPS = {
    'normal': {'program': None, 'overlays': [],
               'roots': ['C.' + n for n in C_NEW] + ['JetForward.' + Path(p).stem for p in PATHS if p.startswith('Coq/forward/proofs/') and p.endswith('.v')]},
    'bitcoin': {'program': 'jets_bitcoin_env', 'overlays': ['bitcoin-env'],
                'roots': ['C.jet_bitcoin_env_relations_indexed', 'C.jet_bitcoin_env_relations_tappath',
                          'C.jet_bitcoin_env_raw_exists', 'C.jet_bitcoin_env_startup_kept',
                          'BitcoinEnvStartup.jet_bitcoin_env_startup_init']},
    'elements-sha': {'program': 'jets_elements', 'overlays': ['elements-sha'],
                     'roots': ['C.' + Path(p).stem for p in PATHS if p.startswith('Coq/elements-sha/C/') and p.endswith('.v')]
                              + ['ElementsStartup.' + Path(p).stem for p in PATHS if p.startswith('Coq/elements-sha/startup/') and p.endswith('.v')]},
    'elements-env': {'program': 'jets_elements_env', 'overlays': ['elements-sha', 'elements-env'],
                     'roots': ['C.' + Path(p).stem for p in PATHS if p.startswith('Coq/elements-env/C/') and p.endswith('.v')]},
}
NS = {'JetStartup': 'Coq/startup/proofs', 'JetForward': 'Coq/forward/proofs',
      'BitcoinEnvStartup': 'Coq/bitcoin-env/startup', 'ElementsStartup': 'Coq/elements-sha/startup'}


@lru_cache(maxsize=None)
def blob(path):
    return subprocess.check_output(['git', 'show', COMMIT + ':' + path], cwd=REPO)


def changed(changes):
    filtered = {p: s for p, s in changes.items() if not p.exists() or p.read_text().splitlines() != s.splitlines()}
    if filtered:
        patcher.patch_files(filtered)


def index_hash():
    return sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO))


def safe_source(source, origin):
    code = scanner.code_only(source)
    if scanner.violations(source) or re.search(r'\b(?:vm_cast_no_check|native_cast_no_check)\b', code):
        raise ValueError('forbidden proof construct: ' + origin)
    return code


def input_map():
    result = {}
    for label, root, suffixes in [
        ('Coq', REPO / 'Coq', {'.v', '.c', '.sh', '.py', '.txt', '.tsv', '.expected'}),
        ('C', REPO / 'C', {'.c', '.h', '.inc', '.S', '.s'}),
        ('Haskell', REPO / 'Haskell', {'.hs'}),
    ]:
        for p in sorted(root.rglob('*')):
            if p.is_file() and '__pycache__' not in p.parts and (
                p.suffix in suffixes or p.name.startswith('_CoqProject') or p.name == 'clightgen-linux.ini.in'
            ):
                result[label + '/' + str(p.relative_to(root))] = sha(p.read_bytes())
    return result


def freeze_baseline():
    path = HERE / 'BASELINE.json'
    data = {'input_sha256': inputs.fingerprint(REPO / 'Coq', REPO),
            'staged_patch_sha256': index_hash(), 'inputs': input_map()}
    if path.exists() and json.loads(path.read_text()) != data:
        raise ValueError('do not overwrite a different baseline')
    changed({path: json.dumps(data, indent=2) + '\n'})
    print('Baseline pinned: ' + data['input_sha256'])


def preservation():
    baseline = json.loads((HERE / 'BASELINE.json').read_text())
    if index_hash() != baseline['staged_patch_sha256']:
        raise ValueError('preexisting staged patch changed')
    expected = dict(baseline['inputs'])
    for p in HERE.glob('*/INSTALLATION.json'):
        for path, digest in json.loads(p.read_text())['sources'].items():
            if path in expected and expected[path] != digest:
                raise ValueError('import overwrote existing source: ' + path)
            expected[path] = digest
    if input_map() != expected:
        raise ValueError('main inputs changed beyond the reviewed additive imports')
    return baseline


def roots_for(group, baseline):
    if group != 'normal':
        return GROUPS[group]['roots']
    roots = ['C.' + Path(p).stem for p in PATHS if p.startswith('Coq/C/') and p.endswith('.v')
             and p not in baseline['inputs'] and Path(p).stem not in ['jets_elements_env', 'jet_frame_constructible_secp']]
    roots += ['JetForward.' + Path(p).stem for p in PATHS if p.startswith('Coq/forward/proofs/') and p.endswith('.v')]
    return roots


def prepare(group):
    config = GROUPS[group]
    baseline = preservation() if (HERE / 'BASELINE.json').exists() else None
    roots = roots_for(group, baseline) if baseline else config['roots']
    work = Path(tempfile.mkdtemp(prefix='jet-remainder-' + group + '.', dir='/tmp')).resolve()
    coq = work / 'Coq'
    shutil.copytree(REPO / 'Coq/Simplicity', coq / 'Simplicity')
    shutil.copy2(REPO / 'Coq/build-jets.sh', coq / 'build-jets.sh')
    # Production sources are read-only inputs of the regenerator.
    for name in ['C', 'Haskell']:
        (work / name).symlink_to(REPO / name, target_is_directory=True)
    overlays = {}
    for folder in config['overlays']:
        overlays.update({Path(p).stem: p for p in PATHS if p.startswith('Coq/' + folder + '/C/') and p.endswith('.v')})
    entries, order, seen, visiting, sources, affected = [], [], set(), set(), {}, {}
    def visit(logical):
        if logical in seen:
            return
        if logical in visiting:
            raise ValueError('cyclic source graph: ' + logical)
        visiting.add(logical)
        ns, name = logical.rsplit('.', 1)
        if ns == 'C':
            origin = ('Coq/C/' + config['program'] + '.v') if name == 'jets_sha' and config['program'] else overlays.get(name, 'Coq/C/' + name + '.v')
            raw = blob(origin) if origin in PATH_SET else (REPO / origin).read_bytes()
        elif ns == 'JetStartupReview':
            origin = 'proof-work/sha-support/' + name + '.v.source'
            raw = (REPO / origin).read_bytes()
        else:
            origin = NS[ns] + '/' + name + '.v'
            raw = blob(origin)
        code = safe_source(raw.decode(), origin)
        deps = sorted(set(re.findall(r'\b((?:C|JetStartupReview|JetStartup|JetForward|BitcoinEnvStartup|ElementsStartup)\.[\w\']+)', code)))
        deps = [d for d in deps if d != logical]
        for dep in deps:
            visit(dep)
        relative = ns + '/' + name + '.v'
        local = REPO / origin
        if local.exists() and local.read_bytes() != raw:
            raise ValueError('existing source collision: ' + origin)
        sources[coq / relative] = raw.decode()
        # Only modules independent of the substituted program may use normal objects.
        affected[logical] = bool(config['program']) and (logical == 'C.jets_sha' or any(affected[d] for d in deps))
        entries.append({'logical': logical, 'origin': origin, 'relative': relative, 'sha256': sha(raw),
                        'dependencies': deps, 'affected': affected[logical],
                        'new': (origin not in baseline['inputs'] and ns != 'JetStartupReview') if baseline else not local.exists(),
                        'results': re.findall(r"^(?:Theorem|Lemma|Corollary|Fact)\s+([\w']+)", code, re.M),
                        'definitions': re.findall(r"^(?:Definition|Fixpoint|CoFixpoint|Inductive|Record)\s+([\w']+)", code, re.M)})
        order.append(relative)
        seen.add(logical)
        visiting.remove(logical)
    for root in roots:
        visit(root)
    # Keep program provenance/regeneration inputs at their original paths.
    extra = [p for p in PATHS if p.startswith('Coq/C/') and p.endswith(('.c', '.sh', '.py'))]
    extra += ['Coq/C/clightgen-linux.ini.in', 'Coq/C/regenerate-elements-jets.sh', 'Coq/C/jet_sha_translation_unit.c']
    for path in sorted(set(extra)):
        raw = blob(path)
        sources[work / path] = raw.decode()
    for program in ['jets_bitcoin_env', 'jets_elements', 'jets_elements_env', 'memcpy_exact', 'memcpy_impl', 'memcmp_impl']:
        path = 'Coq/C/' + program + '.v'
        if path in PATH_SET:
            sources[work / path] = blob(path).decode()
    namespaces = sorted({e['logical'].rsplit('.', 1)[0] for e in entries})
    project = '-Q Simplicity Simplicity\n' + ''.join('-Q ' + n + ' ' + n + '\n' for n in namespaces)
    project += '\n'.join([str(p.relative_to(coq)) for p in sorted((coq / 'Simplicity').rglob('*.v'))] + order) + '\n'
    meta = {'group': group, 'candidate': str(work), 'source_commit': COMMIT, 'roots': roots,
            'modules': entries, 'baseline_input_sha256': baseline['input_sha256'] if baseline else inputs.fingerprint(REPO / 'Coq', REPO),
            'staged_patch_sha256': index_hash(), 'normal_registration': False, 'coverage_added': 0}
    sources[coq / '_CoqProject.jets'] = project
    sources[work / 'ASSEMBLY.json'] = json.dumps(meta, indent=2) + '\n'
    changed(sources)
    # All objects of a substituted C program are rebuilt, unless the previous
    # checked environment unit supplies an exact hash-pinned object.
    prior = json.loads((HERE.parent / 'bitcoin-composition-integration/REVIEW.json').read_text())
    prior_work = Path(prior['candidate'])
    reused = {}
    for e in entries:
        target = coq / e['relative']
        source = REPO / e['origin']
        key = 'Coq/' + e['relative'].replace('.v', '.vo')
        if group == 'bitcoin' and key in prior['evidence_sha256']:
            obj = prior_work / key
            if sha(obj.read_bytes()) != prior['evidence_sha256'][key] or obj.with_suffix('.v').read_bytes() != target.read_bytes():
                raise ValueError('checked prefix drift: ' + key)
            source = obj.with_suffix('.v')
            reused[key] = prior['evidence_sha256'][key]
        elif e['affected'] or e['new'] or not source.exists() or source.suffix != '.v' or e['logical'].split('.')[0] != 'C':
            continue
        stamp = source.stat()
        os.utime(target, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        for suffix in ['.vo', '.vos', '.vok', '.glob']:
            obj = source.with_suffix(suffix)
            if obj.exists():
                shutil.copy2(obj, target.with_suffix(suffix))
    meta['reused_checked_objects'] = reused
    changed({work / 'ASSEMBLY.json': json.dumps(meta, indent=2) + '\n'})
    print(json.dumps({'candidate': str(work), 'group': group, 'modules': len(entries),
                      'new_sources': sum(e['new'] for e in entries)}, indent=2))


def run(work, command, stem, timeout=5400):
    with (work / (stem + '.log')).open('wb') as log:
        result = subprocess.run(command, cwd=work / 'Coq', env=ENV, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('failed ' + stem + '; see ' + str(work / (stem + '.log')))
    return {'command': command, 'exit_code': 0, 'log_sha256': sha((work / (stem + '.log')).read_bytes())}


def inventories(meta):
    selected = [e for e in meta['modules'] if e['new'] or e['origin'].startswith(
        ('Coq/bitcoin-env/', 'Coq/elements-env/', 'Coq/elements-sha/'))]
    return ([e['logical'] + '.' + n for e in selected for n in e['results']],
            [e['logical'] + '.' + n for e in selected for n in e['definitions']])


def namespace_flags(meta):
    paths = sorted({e['logical'].rsplit('.', 1)[0] for e in meta['modules'] if not e['logical'].startswith('C.')})
    return [arg for ns in paths for arg in ['-Q', ns, ns]]


def check(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    for e in meta['modules']:
        if sha((work / 'Coq' / e['relative']).read_bytes()) != e['sha256']:
            raise ValueError('staged source drift')
    for p, value in meta['reused_checked_objects'].items():
        if sha((work / p).read_bytes()) != value:
            raise ValueError('checked object drift')
    flags = namespace_flags(meta)
    asts = []
    programs = {'normal': ['elements-jets', 'memcpy-exact', 'memcpy-impl'],
                'bitcoin': ['bitcoin-env'], 'elements-sha': ['elements-jets'],
                'elements-env': ['elements-env']}[meta['group']]
    names = {'elements-jets': 'jets_elements', 'bitcoin-env': 'jets_bitcoin_env', 'elements-env': 'jets_elements_env',
             'memcpy-exact': 'memcpy_exact', 'memcpy-impl': 'memcpy_impl'}
    for name in programs:
        target = work / ('regenerated-' + name + '.v')
        evidence = run(work, ['bash', 'C/regenerate-' + name + '.sh', str(target)], 'ast-' + name, 120)
        if target.read_bytes() != (work / 'Coq/C' / (names[name] + '.v')).read_bytes():
            raise ValueError('production/reference AST differs: ' + name)
        asts.append(evidence)
    if meta['group'] == 'normal':
        # The reference memcmp has the same pinned target/header/profile as
        # memcpy; Claude did not provide a separate regenerator for it.
        script = (work / 'Coq/C/regenerate-memcpy-impl.sh').read_text().replace('memcpy_impl', 'memcmp_impl')
        changed({work / 'Coq/C/regenerate-memcmp-impl.sh': script})
        target = work / 'regenerated-memcmp-impl.v'
        evidence = run(work, ['bash', 'C/regenerate-memcmp-impl.sh', str(target)], 'ast-memcmp-impl', 120)
        if target.read_bytes() != (work / 'Coq/C/memcmp_impl.v').read_bytes():
            raise ValueError('reference memcmp AST differs')
        asts.append(evidence)
    print('AST correspondence passed: ' + meta['group'], flush=True)
    build = run(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Build passed: ' + meta['group'], flush=True)
    # Report all newly imported declarations and all derived-unit sources.
    selected = [e for e in meta['modules'] if e['new'] or e['origin'].startswith(('Coq/bitcoin-env/', 'Coq/elements-env/', 'Coq/elements-sha/'))]
    results, definitions = inventories(meta)
    prefix = ['Set Warnings "-notation-overridden".'] + ['Require ' + e['logical'] + '.' for e in selected]
    a = prefix[:]
    for n in results:
        a += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    d = prefix + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    for kind, n in wanted:
        d += ['Goal True. idtac "REMAINDER_' + kind + ' ' + n + '". exact I. Qed.', ('Check ' if kind == 'TYPE' else 'Print ') + n + '.']
    changed({work / 'assumptions.v': '\n'.join(a) + '\n', work / 'contracts.v': '\n'.join(d) + '\n'})
    ar = run(work, ['bash', 'build-jets.sh', '--coqc'] + flags + ['-q', str(work / 'assumptions.v')], 'assumptions', 3600)
    dependencies = reports.assumptions((work / 'assumptions.log').read_text())
    if set(dependencies) != set(results) or any(not ds <= EIGHT for ds in dependencies.values()):
        raise ValueError('missing/unreviewed theorem assumptions')
    cr = run(work, ['bash', 'build-jets.sh', '--coqc'] + flags + ['-q', str(work / 'contracts.v')], 'contracts', 1800)
    txt = (work / 'contracts.log').read_text()
    if '...' in txt or re.findall(r'(?m)^REMAINDER_(TYPE|DEF) (\S+)$', txt) != wanted:
        raise ValueError('incomplete/truncated type/definition report')
    kr = run(work, ['bash', 'build-jets.sh', '--coqchk'] + flags + ['-o'] + meta['roots'], 'kernel', 10800)
    kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    evidence = {str(p.relative_to(work)): sha(p.read_bytes()) for p in work.rglob('*')
                if p.is_file() and (p.suffix in ['.vo', '.log'] or p.name in ['assumptions.v', 'contracts.v'])}
    receipt = {'source_commit': COMMIT, 'group': meta['group'], 'candidate': str(work),
               'assembly_sha256': sha((work / 'ASSEMBLY.json').read_bytes()),
               'AST': asts, 'build': build, 'assumptions': ar, 'contracts': cr, 'kernel': kr,
               'results': len(results), 'definitions': len(definitions), 'closed_results': sum(not ds for ds in dependencies.values()),
               'expected_dependencies': {n: sorted(ds) for n, ds in dependencies.items()}, 'evidence_sha256': evidence,
               'normal_registration': False, 'coverage_added': 0, 'canonical_source_review': 'partial; no new admission'}
    changed({work / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n'})
    print(json.dumps({k: v for k, v in receipt.items() if k not in ['expected_dependencies', 'evidence_sha256']}, indent=2))


def review(work, seal=False):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if (receipt['source_commit'] != COMMIT or meta['source_commit'] != COMMIT
            or receipt['group'] != meta['group'] or receipt['candidate'] != str(work)
            or receipt.get('normal_registration') is not False or receipt.get('coverage_added') != 0
            or receipt.get('canonical_source_review') != 'partial; no new admission'):
        raise ValueError('receipt scope drift')
    assembly_hash = sha((work / 'ASSEMBLY.json').read_bytes())
    if receipt.get('assembly_sha256') != assembly_hash and not (seal and 'assembly_sha256' not in receipt):
        raise ValueError('assembly metadata drift')
    baseline = preservation()
    if (meta['baseline_input_sha256'] != baseline['input_sha256']
            or meta['staged_patch_sha256'] != baseline['staged_patch_sha256']):
        raise ValueError('audit baseline mismatch')
    config = GROUPS[meta['group']]
    roots = roots_for(meta['group'], baseline)
    if meta['roots'] != roots:
        raise ValueError('recursive kernel root scope drift')
    by_name = {e['logical']: e for e in meta['modules']}
    if len(by_name) != len(meta['modules']):
        raise ValueError('duplicate module inventory')
    visited = set()
    def walk(logical):
        if logical in visited:
            return
        if logical not in by_name:
            raise ValueError('missing dependency: ' + logical)
        visited.add(logical)
        for dep in by_name[logical]['dependencies']:
            walk(dep)
    for root in roots:
        walk(root)
    if visited != set(by_name):
        raise ValueError('extraneous modules in dependency inventory')
    results, definitions = inventories(meta)
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    contracts = (work / 'contracts.log').read_text()
    if '...' in contracts or re.findall(r'(?m)^REMAINDER_(TYPE|DEF) (\S+)$', contracts) != wanted:
        raise ValueError('incomplete contract inventory')
    dependencies = reports.assumptions((work / 'assumptions.log').read_text())
    if (set(dependencies) != set(results)
            or {n: sorted(ds) for n, ds in dependencies.items()} != receipt['expected_dependencies']
            or any(not ds <= EIGHT for ds in dependencies.values())
            or receipt['results'] != len(results) or receipt['definitions'] != len(definitions)
            or receipt['closed_results'] != sum(not ds for ds in dependencies.values())):
        raise ValueError('missing/changed/unreviewed theorem assumptions')
    flags = namespace_flags(meta)
    commands = {
        'build': ['bash', 'build-jets.sh', '-j2'],
        'assumptions': ['bash', 'build-jets.sh', '--coqc'] + flags + ['-q', str(work / 'assumptions.v')],
        'contracts': ['bash', 'build-jets.sh', '--coqc'] + flags + ['-q', str(work / 'contracts.v')],
        'kernel': ['bash', 'build-jets.sh', '--coqchk'] + flags + ['-o'] + meta['roots'],
    }
    for stem, command in commands.items():
        proof = receipt[stem]
        if proof['exit_code'] != 0 or proof['command'] != command or proof['log_sha256'] != sha((work / (stem + '.log')).read_bytes()):
            raise ValueError('command/terminal evidence drift: ' + stem)
    if 'integration_corruption_tests' in receipt:
        proof = receipt['integration_corruption_tests']
        command = [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)]
        if (proof['exit_code'] != 0 or proof['command'] != command
                or proof['log_sha256'] != sha((work / 'review-fixtures.log').read_bytes())
                or (work / 'review-fixtures.log').read_text().strip() !=
                'Remainder corruption fixtures passed: 13; lexical fixtures passed: 6'):
            raise ValueError('review corruption-test evidence drift')
    kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    for relative, digest in receipt['evidence_sha256'].items():
        path = work / relative
        if path.is_symlink() or not path.is_relative_to(work) or sha(path.read_bytes()) != digest:
            raise ValueError('artifact evidence drift: ' + relative)
    compiled = set(re.findall(r'(?m)^COQC (\S+\.v)$', (work / 'build.log').read_text()))
    additions = {}
    overlays = {}
    for folder in config['overlays']:
        overlays.update({Path(p).stem: p for p in PATHS if p.startswith('Coq/' + folder + '/C/') and p.endswith('.v')})
    for e in meta['modules']:
        ns, name = e['logical'].rsplit('.', 1)
        if ns == 'C':
            origin = ('Coq/C/' + config['program'] + '.v') if name == 'jets_sha' and config['program'] else overlays.get(name, 'Coq/C/' + name + '.v')
        elif ns == 'JetStartupReview':
            origin = 'proof-work/sha-support/' + name + '.v.source'
        else:
            origin = NS[ns] + '/' + name + '.v'
        if origin != e['origin'] or e['relative'] != ns + '/' + name + '.v' or e['new'] != (origin not in baseline['inputs'] and not (ns == 'JetStartupReview')):
            raise ValueError('module source/program binding drift')
        source = work / 'Coq' / e['relative']
        raw = source.read_bytes()
        if sha(raw) != e['sha256']:
            raise ValueError('staged source drift: ' + e['origin'])
        if e['origin'] in PATH_SET and raw != blob(e['origin']):
            raise ValueError('frozen source provenance drift')
        code = safe_source(raw.decode(), e['origin'])
        deps = sorted(set(re.findall(r'\b((?:C|JetStartupReview|JetStartup|JetForward|BitcoinEnvStartup|ElementsStartup)\.[\w\']+)', code)) - {e['logical']})
        if deps != e['dependencies']:
            raise ValueError('source dependency graph drift')
        if (re.findall(r"^(?:Theorem|Lemma|Corollary|Fact)\s+([\w']+)", code, re.M) != e['results']
                or re.findall(r"^(?:Definition|Fixpoint|CoFixpoint|Inductive|Record)\s+([\w']+)", code, re.M) != e['definitions']):
            raise ValueError('source declaration inventory drift')
        if e['new']:
            if e['relative'] not in compiled:
                raise ValueError('new source was not freshly compiled: ' + e['origin'])
            additions[e['origin']] = raw.decode()
        elif sha((REPO / e['origin']).read_bytes()) != e['sha256']:
            raise ValueError('inherited source drift')
        vo = 'Coq/' + str(Path(e['relative']).with_suffix('.vo'))
        if vo not in receipt['evidence_sha256']:
            raise ValueError('unbound compiled module: ' + vo)
    programs = {
        'normal': [('elements-jets', 'jets_elements'), ('memcpy-exact', 'memcpy_exact'),
                   ('memcpy-impl', 'memcpy_impl'), ('memcmp-impl', 'memcmp_impl')],
        'bitcoin': [('bitcoin-env', 'jets_bitcoin_env')],
        'elements-sha': [('elements-jets', 'jets_elements')],
        'elements-env': [('elements-env', 'jets_elements_env')],
    }[meta['group']]
    if len(receipt['AST']) != len(programs):
        raise ValueError('missing AST correspondence check')
    for evidence, (name, program) in zip(receipt['AST'], programs):
        if (evidence['exit_code'] != 0
                or evidence['command'] != ['bash', 'C/regenerate-' + name + '.sh', str(work / ('regenerated-' + name + '.v'))]
                or evidence['log_sha256'] != sha((work / ('ast-' + name + '.log')).read_bytes())
                or (work / ('regenerated-' + name + '.v')).read_bytes() != blob('Coq/C/' + program + '.v')):
            raise ValueError('AST correspondence evidence drift')
    # Reference C inputs and their regenerators are part of the review,
    # not standalone proof claims. Original broad build scripts are omitted:
    # this driver supplies copied, isolated namespaces instead.
    extras = {
        'normal': ['jet_memcpy_exact.c', 'jet_memcpy_impl.c', 'jet_memcmp_impl.c',
                   'regenerate-memcpy-exact.sh', 'regenerate-memcpy-impl.sh'],
        'elements-env': ['jet_elements_env_translation_unit.c', 'regenerate-elements-env.sh'],
        'bitcoin': [], 'elements-sha': [],
    }[meta['group']]
    for name in extras:
        origin = 'Coq/C/' + name
        raw = blob(origin)
        if (work / origin).read_bytes() != raw:
            raise ValueError('regenerator/input provenance drift')
        if not (REPO / origin).exists():
            additions[origin] = raw.decode()
        elif (REPO / origin).read_bytes() != raw:
            raise ValueError('reference/production input collision')
    if seal:
        receipt['assembly_sha256'] = assembly_hash
        receipt['integration_review_driver_sha256'] = sha(Path(__file__).read_bytes())
        changed({work / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n'})
    return meta, receipt, additions


def archive(work):
    meta, receipt, _ = review(work)
    if 'integration_corruption_tests' not in receipt:
        receipt['integration_corruption_tests'] = run(work,
            [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)], 'review-fixtures', 180)
        changed({work / 'REVIEW.json': json.dumps(receipt, indent=2) + '\n'})
    review(work)
    changed({HERE / meta['group'] / name: (work / name).read_text()
             for name in ['ASSEMBLY.json', 'REVIEW.json']})
    print('Completed review archived: ' + meta['group'])


def install(work):
    archive(work)
    meta, receipt, additions = review(work)
    group_dir = HERE / meta['group']
    sources = {p: sha(s.encode()) for p, s in additions.items()}
    new_paths = sorted(p for p in additions if not (REPO / p).exists())
    for origin, source in additions.items():
        target = REPO / origin
        if target.exists() and target.read_text() != source:
            raise ValueError('additive installation collision')
    changes = {REPO / p: s for p, s in additions.items()}
    for name in ['ASSEMBLY.json', 'REVIEW.json']:
        changes[group_dir / name] = (work / name).read_text()
    changes[group_dir / 'INSTALLATION.json'] = json.dumps({
        'source_commit': COMMIT, 'group': meta['group'], 'sources': sources, 'new_paths': new_paths,
        'review_sha256': sha((work / 'REVIEW.json').read_bytes()),
        'current_whole_worktree_full_acceptance': False,
        'normal_registration': False, 'coverage_added': 0,
    }, indent=2) + '\n'
    changed(changes)
    preservation()
    print(json.dumps({'group': meta['group'], 'verified_sources': len(sources), 'new_files_added': len(new_paths),
                      'normal_registration': False, 'coverage_added': 0}, indent=2))


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('mode', choices=['prepare', 'check', 'freeze-baseline', 'seal', 'review', 'archive', 'install', 'post-check'])
    cli.add_argument('--group', choices=GROUPS)
    cli.add_argument('--candidate', type=Path)
    args = cli.parse_args()
    if args.mode == 'freeze-baseline':
        freeze_baseline()
    elif args.mode == 'post-check':
        preservation()
        for path in HERE.glob('*/ASSEMBLY.json'):
            review(Path(json.loads(path.read_text())['candidate']))
        print('Installed sources, audit artifacts and preexisting inputs preserved')
    elif args.mode == 'prepare':
        prepare(args.group)
    elif args.mode == 'check':
        check(args.candidate.resolve())
    elif args.mode in ['review', 'seal']:
        meta, receipt, additions = review(args.candidate.resolve(), seal=args.mode == 'seal')
        print(json.dumps({'group': meta['group'], 'sources': sorted(additions)}, indent=2))
    elif args.mode == 'archive':
        archive(args.candidate.resolve())
    else:
        install(args.candidate.resolve())
