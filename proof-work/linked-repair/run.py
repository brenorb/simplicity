"""Checked linked-program integrations in copied, program-specific Coq trees.

No original-program contract or registry is changed. Three frozen unchecked
conversion proofs are replaced by bounded checked conversions before staging.
"""
import argparse
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
spec = importlib.util.spec_from_file_location('linked_previous', HERE.parent / 'claude-remainder-integration/run.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
COMMIT = old.COMMIT
GROUPS = {
    'core': ['C.jet_linked_program', 'C.jet_linked_memcpy_jets', 'C.jet_frame_executable_linked'],
    'sha': ['C.' + Path(p).stem for p in old.PATHS if p.startswith('Coq/linked/C/')
            and p.endswith('_linked.v') and Path(p).stem != 'jet_frame_executable_linked']
           + ['C.jet_linked_sha_program', 'JetStartup.jet_sha_startup_linked'],
    'bitcoin': ['C.jet_bitcoin_env_linked_program', 'C.jet_bitcoin_env_linked'],
}
CORE_PATCHES = ['jet_copyBits_memcpy_exec', 'jet_copyBits_memcpy_helper', 'jet_copyBits_wide_memcpy']
SHA_PATCHES = ['jet_sha_uchars_prep', 'jet_sha_uchars_loop']
PROOF_PATTERN = (r'Proof\. vm_cast_no_check \(@eq_refl \(option \(list '
                 r'\(ident \* globdef Clight\.fundef type\)\)\)\s*'
                 r'\(Some \(PTree\.elements \(prog_defmap linked_ast\)\)\)\)\. Qed\.')


def json_write(path, data):
    old.changed({path: json.dumps(data, indent=2) + '\n'})


def repair(raw):
    text, count = re.subn(PROOF_PATTERN, 'Proof. timeout 10 (vm_compute; reflexivity). Qed.', raw.decode())
    if count != 1:
        raise ValueError('expected exactly one frozen conversion proof')
    old.safe_source(text, 'checked linking repair')
    return text.encode()


def freeze():
    old.preservation()
    data = {'inputs': old.input_map(), 'staged_patch_sha256': old.index_hash(),
            'source_commit': COMMIT, 'main_head': subprocess.check_output(
                ['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()}
    path = HERE / 'BASELINE.json'
    if path.exists() and json.loads(path.read_text()) != data:
        raise ValueError('do not replace a different baseline')
    json_write(path, data)


def preservation():
    data = json.loads((HERE / 'BASELINE.json').read_text())
    if old.index_hash() != data['staged_patch_sha256']:
        raise ValueError('preexisting staged patch changed')
    expected = dict(data['inputs'])
    for p in HERE.glob('*/INSTALLATION.json'):
        for name, digest in json.loads(p.read_text())['sources'].items():
            if name in expected and expected[name] != digest:
                raise ValueError('source overwrite: ' + name)
            expected[name] = digest
    if expected != old.input_map():
        raise ValueError('main proof inputs changed outside additive installations')
    return data


def command(work, args, stem, deadline=5400):
    return old.run(work, args, stem, deadline)


def assemble(work, group):
    """Deterministic dependency inventory; also used to validate every receipt."""
    baseline = preservation()
    coq = work / 'Coq'
    scripts = {n: old.blob('Coq/linked/' + n) for n in ['gen-jets.py', 'patch-consumers.py']}
    scratch = Path(tempfile.mkdtemp(prefix='jet-link-transform.', dir='/tmp')).resolve()
    supplemental = {work / n: b.decode() for n, b in scripts.items()}
    old.changed({scratch / n: b.decode() for n, b in scripts.items()})
    core = (REPO / 'Coq/C/jets.v').read_bytes()
    reference = (REPO / 'Coq/C/memcpy_exact.v').read_bytes()
    original_program = {'sha': 'jets_sha', 'bitcoin': 'jets_bitcoin_env'}.get(group)
    program_alias = {'sha': 'jets_sha_unlinked', 'bitcoin': 'jets_bitcoin_env'}.get(group)
    aliases = {'jets_unlinked': ('Coq/C/jets.v', core), 'memcpy_exact': ('Coq/C/memcpy_exact.v', reference)}
    if original_program:
        path = 'Coq/C/' + original_program + '.v'
        aliases[program_alias] = (path, (REPO / path).read_bytes())
    supplemental.update({work / 'inputs' / (name + '.v'): b.decode() for name, (_, b) in aliases.items()})
    old.changed({scratch / 'inputs' / (name + '.v'): b.decode() for name, (_, b) in aliases.items()})
    generated = {}
    for name, original in [('jets', 'jets_unlinked')] + ([('jets_sha', program_alias)] if original_program else []):
        dest = scratch / 'generated' / (name + '.v')
        dest.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([sys.executable, '-B', str(scratch / 'gen-jets.py'), str(scratch / 'inputs' / (original + '.v')),
                        str(scratch / 'inputs/memcpy_exact.v'), str(dest)], check=True, timeout=30)
        generated[name] = dest.read_bytes()
    patches = CORE_PATCHES + (SHA_PATCHES if original_program else [])
    # The supplied patcher expects five inputs, even for a core-only closure.
    old.changed({scratch / 'patch-inputs' / (n + '.v'): (REPO / ('Coq/C/' + n + '.v')).read_text()
                 for n in CORE_PATCHES + SHA_PATCHES})
    (scratch / 'patched').mkdir()
    subprocess.run([sys.executable, '-B', str(scratch / 'patch-consumers.py'), str(scratch / 'patch-inputs'),
                    str(scratch / 'patched')], check=True, timeout=30)
    overlays = {Path(p).stem: p for p in old.PATHS if p.startswith('Coq/linked/C/') and p.endswith('.v')}
    if group == 'bitcoin':
        overlays.update({Path(p).stem: p for p in old.PATHS if p.startswith(
            ('Coq/bitcoin-env/C/', 'Coq/bitcoin-env-linked/C/')) and p.endswith('.v')})
    entries, staged, seen, visiting = [], supplemental, set(), set()
    def visit(logical):
        if logical in seen:
            return
        if logical in visiting:
            raise ValueError('source cycle')
        visiting.add(logical)
        ns, name = logical.rsplit('.', 1)
        transform = 'identity'
        if ns == 'C' and name in generated:
            origin = 'Coq/C/' + ('jets' if name == 'jets' else original_program) + '.v'
            raw = generated[name]
            source_hash = old.sha((REPO / origin).read_bytes())
            transform = 'link-memcpy-exact'
        elif ns == 'C' and name in aliases:
            origin, raw = aliases[name]
            source_hash = old.sha(raw)
        elif ns == 'C' and name in patches:
            origin = 'Coq/C/' + name + '.v'
            source_hash = old.sha((REPO / origin).read_bytes())
            raw = (scratch / 'patched' / (name + '.v')).read_bytes()
            transform = 'internal-memcpy-callsite'
        else:
            if ns == 'C':
                origin = overlays.get(name, 'Coq/C/' + name + '.v')
            elif ns == 'JetStartupReview':
                origin = 'proof-work/sha-support/' + name + '.v.source'
            elif ns == 'JetStartup':
                origin = ('Coq/linked/startup/' if name == 'jet_sha_startup_linked' else 'Coq/startup/proofs/') + name + '.v'
            else:
                raise ValueError('unexpected namespace ' + ns)
            raw = old.blob(origin) if origin in old.PATH_SET else (REPO / origin).read_bytes()
            source_hash = old.sha(raw)
            if name in ['jet_linked_program', 'jet_linked_sha_program', 'jet_bitcoin_env_linked_program']:
                raw = repair(raw)
                transform = 'checked-conversion-proof'
            if (REPO / origin).exists() and raw != (REPO / origin).read_bytes():
                raise ValueError('frozen/current source collision ' + origin)
        code = old.safe_source(raw.decode(), origin)
        deps = sorted(set(re.findall(r"\b((?:C|JetStartupReview|JetStartup)\.[\w']+)", code)) - {logical})
        for d in deps:
            visit(d)
        affected = logical in ['C.jets', 'C.jets_sha', 'C.jet_memcpy_model'] or transform != 'identity'
        affected = affected or (ns == 'C' and name in aliases and Path(origin).stem != name)
        affected = affected or any(e['affected'] for e in entries if e['logical'] in deps)
        relative = ns + '/' + name + '.v'
        new = origin not in baseline['inputs'] and ns != 'JetStartupReview'
        selected = origin.startswith(('Coq/linked/', 'Coq/bitcoin-env-linked/')) or (new and ns == 'JetStartup')
        e = {'logical': logical, 'relative': relative, 'origin': origin, 'sha256': old.sha(raw),
             'source_sha256': source_hash, 'transform': transform, 'dependencies': deps,
             'affected': affected, 'new': new, 'selected': selected,
             'results': re.findall(r"^(?:Theorem|Lemma|Corollary|Fact)\s+([\w']+)", code, re.M),
             'definitions': re.findall(r"^(?:Definition|Fixpoint|CoFixpoint|Inductive|Record)\s+([\w']+)", code, re.M)}
        entries.append(e)
        staged[coq / relative] = raw.decode()
        seen.add(logical)
        visiting.remove(logical)
    for root in GROUPS[group]:
        visit(root)
    # Regenerators write to explicit temporary targets only; production C is
    # a read-only input symlink, never a compiler-output namespace symlink.
    for p in (REPO / 'Coq/C').iterdir():
        if p.suffix in ['.c', '.sh'] or p.name == 'clightgen-linux.ini.in':
            staged[work / 'Coq/C' / p.name] = p.read_text()
    namespaces = sorted({e['logical'].rsplit('.', 1)[0] for e in entries})
    project = '-Q Simplicity Simplicity\n' + ''.join('-Q ' + n + ' ' + n + '\n' for n in namespaces)
    project += '\n'.join([str(p.relative_to(coq)) for p in sorted((coq / 'Simplicity').rglob('*.v'))]
                         + [e['relative'] for e in entries]) + '\n'
    staged[coq / '_CoqProject.jets'] = project
    meta = {'group': group, 'roots': GROUPS[group], 'source_commit': COMMIT,
            'candidate': str(work), 'modules': entries, 'scripts': {n: old.sha(b) for n, b in scripts.items()},
            'baseline_sha256': old.sha((HERE / 'BASELINE.json').read_bytes()),
            'normal_registration': False, 'coverage_added': 0}
    return meta, staged


def prepare(group):
    work = Path(tempfile.mkdtemp(prefix='jet-linked-' + group + '.', dir='/tmp')).resolve()
    shutil.copytree(REPO / 'Coq/Simplicity', work / 'Coq/Simplicity')
    shutil.copy2(REPO / 'Coq/build-jets.sh', work / 'Coq/build-jets.sh')
    (work / 'C').symlink_to(REPO / 'C', target_is_directory=True)
    meta, sources = assemble(work, group)
    old.changed(sources)
    reused = {}
    for e in meta['modules']:
        target = work / 'Coq' / e['relative']
        source = REPO / e['origin']
        if e['affected'] or e['new'] or not source.exists() or source.suffix != '.v':
            continue
        if source.with_suffix('.vo').exists():
            stamp = source.stat()
            os.utime(target, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                obj = source.with_suffix(suffix)
                if obj.exists():
                    shutil.copy2(obj, target.with_suffix(suffix))
            reused['Coq/' + str(Path(e['relative']).with_suffix('.vo'))] = old.sha(source.with_suffix('.vo').read_bytes())
    meta['reused_objects'] = reused
    json_write(work / 'ASSEMBLY.json', meta)
    print(json.dumps({'group': group, 'candidate': str(work), 'modules': len(meta['modules'])}), flush=True)


def inventories(meta):
    selected = [e for e in meta['modules'] if e['selected']]
    results = [e['logical'] + '.' + n for e in selected for n in e['results']]
    definitions = [e['logical'] + '.' + n for e in selected for n in e['definitions']]
    # Proof-valued exported definitions are assumption-audited as results too.
    results += [n for n in definitions if n.startswith('C.jet_bitcoin_env_linked.')]
    return selected, results, definitions


def flags(meta):
    return old.namespace_flags(meta)


def policy(name):
    if re.fullmatch(r'C\.jet_(?:linked(?:_sha)?|bitcoin_env_linked)_program\.linked_program_is_(?:link_program|compcert_link)', name):
        return old.EIGHT | {'lib.Axioms.proof_irr'}
    return old.EIGHT


def assumptions(text):
    # Do not widen the inherited normal-registry parser's global allowlist.
    # Coq prints CompCert's axiom here as lib.Axioms.proof_irr; retain that
    # exact spelling and check each result against policy(name) below.
    result, current, mode = {}, None, None
    def finish():
        if current is not None and (mode is None or mode == 'axioms' and not result[current]):
            raise ValueError('unfinished assumption report: ' + current)
    for line in text.splitlines():
        match = re.fullmatch(r'JET_ASSUMPTIONS (\S+)', line)
        if match:
            finish()
            current = match[1]
            if current in result:
                raise ValueError('duplicate assumption marker')
            result[current], mode = set(), None
        elif line == 'Axioms:':
            if current is None or mode is not None:
                raise ValueError('unexpected axiom section')
            mode = 'axioms'
        elif line == 'Closed under the global context':
            if current is None or mode is not None:
                raise ValueError('unexpected closed section')
            mode = 'closed'
        elif mode == 'axioms' and line and not line[0].isspace():
            result[current].add(line.split()[0])
    finish()
    return result


def audit(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    validate_sources(work, meta)
    ast = []
    programs = [('jets', 'jets_unlinked'), ('memcpy-exact', 'memcpy_exact')]
    if meta['group'] != 'core':
        programs += [('sha-jets', 'jets_sha_unlinked')] if meta['group'] == 'sha' else [('bitcoin-env', 'jets_bitcoin_env')]
    for regen, alias in programs:
        script = 'regenerate-' + regen + '.sh'
        if regen == 'jets':
            script = 'regenerate-jets.sh'
        target = work / ('regenerated-' + alias + '.v')
        evidence = command(work, ['bash', 'C/' + script, str(target)], 'ast-' + alias, 120)
        if target.read_bytes() != (work / 'inputs' / (alias + '.v')).read_bytes():
            raise ValueError('original/reference AST differs: ' + alias)
        ast.append(evidence)
    if (work / 'build.log').exists() and not (work / 'build-initial.log').exists():
        # An interrupted/rejected report can be retried without discarding
        # the fresh compilation trace. The confirming make must still exit 0,
        # and every compiled object is checked recursively afterward.
        shutil.copy2(work / 'build.log', work / 'build-initial.log')
    build = command(work, ['bash', 'build-jets.sh', '-j2'], 'build')
    print('Fresh build passed: ' + meta['group'], flush=True)
    selected, results, definitions = inventories(meta)
    prefix = ['Require ' + e['logical'] + '.' for e in selected]
    a = prefix[:]
    for n in results:
        a += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
    d = prefix + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    for kind, n in wanted:
        d += ['Goal True. idtac "LINKED_' + kind + ' ' + n + '". exact I. Qed.', ('Check ' if kind == 'TYPE' else 'Print ') + n + '.']
    old.changed({work / 'assumptions.v': '\n'.join(a) + '\n', work / 'contracts.v': '\n'.join(d) + '\n'})
    ar = command(work, ['bash', 'build-jets.sh', '--coqc'] + flags(meta) + ['-q', str(work / 'assumptions.v')], 'assumptions')
    deps = assumptions((work / 'assumptions.log').read_text())
    if set(deps) != set(results) or any(not ds <= policy(n) for n, ds in deps.items()):
        raise ValueError('missing/unreviewed assumptions')
    cr = command(work, ['bash', 'build-jets.sh', '--coqc'] + flags(meta) + ['-q', str(work / 'contracts.v')], 'contracts')
    log = (work / 'contracts.log').read_text()
    if '...' in log or re.findall(r'(?m)^LINKED_(TYPE|DEF) (\S+)$', log) != wanted:
        raise ValueError('truncated contract report')
    print('Contracts/assumptions passed; recursive kernel check started: ' + meta['group'], flush=True)
    kr = command(work, ['bash', 'build-jets.sh', '--coqchk'] + flags(meta) + ['-o'] + meta['roots'], 'kernel', 10800)
    old.kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    evidence = {str(p.relative_to(work)): old.sha(p.read_bytes()) for p in work.rglob('*')
                if p.is_file() and (p.suffix in ['.vo', '.log'] or p.name in ['assumptions.v', 'contracts.v'])}
    receipt = {'source_commit': COMMIT, 'group': meta['group'], 'candidate': str(work),
               'assembly_sha256': old.sha((work / 'ASSEMBLY.json').read_bytes()),
               'driver_sha256': old.sha(Path(__file__).read_bytes()), 'AST': ast,
               'build': build, 'assumptions': ar, 'contracts': cr, 'kernel': kr,
               'results': len(results), 'definitions': len(definitions), 'closed_results': sum(not ds for ds in deps.values()),
               'expected_dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'evidence_sha256': evidence,
               'normal_registration': False, 'coverage_added': 0,
               'program_scope': 'derived internally-linked programs only; original libc labels unchanged'}
    json_write(work / 'REVIEW.json', receipt)
    print('Recursive kernel check passed: ' + meta['group'], flush=True)


def validate_sources(work, meta):
    expected, sources = assemble(work, meta['group'])
    actual = dict(meta)
    actual.pop('reused_objects', None)
    if actual != expected:
        raise ValueError('assembly graph/provenance/scope drift')
    for path, text in sources.items():
        if not path.exists() or path.read_text() != text:
            raise ValueError('staged source drift: ' + str(path))
    for name, digest in meta['reused_objects'].items():
        if old.sha((work / name).read_bytes()) != digest:
            raise ValueError('inherited object drift')
    return sources


def review(work):
    meta = json.loads((work / 'ASSEMBLY.json').read_text())
    sources = validate_sources(work, meta)
    receipt = json.loads((work / 'REVIEW.json').read_text())
    if (receipt['assembly_sha256'] != old.sha((work / 'ASSEMBLY.json').read_bytes())
            or receipt['driver_sha256'] != old.sha(Path(__file__).read_bytes())
            or receipt['source_commit'] != COMMIT or receipt['candidate'] != str(work)
            or receipt['group'] != meta['group'] or receipt['normal_registration'] is not False
            or receipt['coverage_added'] != 0):
        raise ValueError('receipt scope/driver drift')
    for relative, digest in receipt['evidence_sha256'].items():
        p = work / relative
        if not p.is_relative_to(work) or p.is_symlink() or old.sha(p.read_bytes()) != digest:
            raise ValueError('terminal/object evidence drift: ' + relative)
    traces = [work / 'build.log'] + ([work / 'build-initial.log'] if (work / 'build-initial.log').exists() else [])
    for trace in traces:
        if str(trace.relative_to(work)) not in receipt['evidence_sha256']:
            raise ValueError('unbound fresh compilation trace')
    compiled = set(re.findall(r'(?m)^COQC (\S+\.v)$', '\n'.join(p.read_text() for p in traces)))
    additions = {}
    for e in meta['modules']:
        if (e['new'] or e['affected']) and e['relative'] not in compiled:
            raise ValueError('program-dependent source was not freshly compiled: ' + e['logical'])
        if 'Coq/' + str(Path(e['relative']).with_suffix('.vo')) not in receipt['evidence_sha256']:
            raise ValueError('missing compiled artifact: ' + e['logical'])
        if e['new'] and e['transform'] in ['identity', 'checked-conversion-proof']:
            additions[e['origin']] = sources[work / 'Coq' / e['relative']]
    _, results, definitions = inventories(meta)
    deps = assumptions((work / 'assumptions.log').read_text())
    if (set(deps) != set(results) or {n: sorted(ds) for n, ds in deps.items()} != receipt['expected_dependencies']
            or any(not ds <= policy(n) for n, ds in deps.items())
            or receipt['results'] != len(results) or receipt['definitions'] != len(definitions)
            or receipt['closed_results'] != sum(not ds for ds in deps.values())):
        raise ValueError('result/assumption inventory drift')
    wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
    txt = (work / 'contracts.log').read_text()
    if '...' in txt or re.findall(r'(?m)^LINKED_(TYPE|DEF) (\S+)$', txt) != wanted:
        raise ValueError('contract inventory drift')
    commands = {'build': ['bash', 'build-jets.sh', '-j2'],
                'assumptions': ['bash', 'build-jets.sh', '--coqc'] + flags(meta) + ['-q', str(work / 'assumptions.v')],
                'contracts': ['bash', 'build-jets.sh', '--coqc'] + flags(meta) + ['-q', str(work / 'contracts.v')],
                'kernel': ['bash', 'build-jets.sh', '--coqchk'] + flags(meta) + ['-o'] + meta['roots']}
    for name, cmd in commands.items():
        r = receipt[name]
        if r['command'] != cmd or r['exit_code'] != 0 or r['log_sha256'] != old.sha((work / (name + '.log')).read_bytes()):
            raise ValueError('command receipt drift')
    original = [('jets', 'jets_unlinked'), ('memcpy-exact', 'memcpy_exact')]
    if meta['group'] != 'core':
        original += [('sha-jets', 'jets_sha_unlinked')] if meta['group'] == 'sha' else [('bitcoin-env', 'jets_bitcoin_env')]
    if len(receipt['AST']) != len(original):
        raise ValueError('missing regenerator receipts')
    for r, (regen, alias) in zip(receipt['AST'], original):
        cmd = ['bash', 'C/regenerate-' + regen + '.sh', str(work / ('regenerated-' + alias + '.v'))]
        if r['command'] != cmd or r['exit_code'] != 0 or r['log_sha256'] != old.sha((work / ('ast-' + alias + '.log')).read_bytes()):
            raise ValueError('regenerator receipt drift')
        if (work / ('regenerated-' + alias + '.v')).read_bytes() != (work / 'inputs' / (alias + '.v')).read_bytes():
            raise ValueError('regenerated input differs')
    old.kernel.kernel((work / 'kernel.log').read_text(), sorted((REPO / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    additions.update({'Coq/linked/' + n: old.blob('Coq/linked/' + n).decode() for n in meta['scripts']})
    return meta, receipt, additions


def install(work):
    meta, receipt, additions = review(work)
    group = 'linked-' + meta['group']
    new_paths = [p for p in additions if not (REPO / p).exists()]
    for p, text in additions.items():
        if (REPO / p).exists() and (REPO / p).read_text() != text:
            raise ValueError('additive import collision: ' + p)
    ledger = {'source_commit': COMMIT, 'group': group,
              'sources': {p: old.sha(s.encode()) for p, s in additions.items()}, 'new_paths': sorted(new_paths),
              'review_sha256': old.sha((work / 'REVIEW.json').read_bytes()),
              'current_whole_worktree_full_acceptance': False, 'normal_registration': False, 'coverage_added': 0}
    changes = {REPO / p: s for p, s in additions.items()}
    changes.update({HERE / meta['group'] / n: (work / n).read_text() for n in ['ASSEMBLY.json', 'REVIEW.json']})
    changes[HERE / meta['group'] / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    # Compose preservation with the preceding source-only integration ledger.
    changes[old.HERE / group / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
    old.changed(changes)
    preservation()
    old.preservation()
    print(json.dumps({'group': group, 'new_files': len(new_paths), 'results': receipt['results'],
                      'coverage_added': 0}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('action', choices=['freeze', 'prepare', 'audit', 'review', 'install', 'post-check'])
    parser.add_argument('target', nargs='?')
    args = parser.parse_args()
    if args.action == 'freeze':
        freeze()
    elif args.action == 'prepare':
        prepare(args.target)
    elif args.action == 'post-check':
        preservation()
        for p in HERE.glob('*/REVIEW.json'):
            review(Path(json.loads(p.read_text())['candidate']))
        print('Linked installation preservation and evidence checks passed')
    else:
        globals()[args.action](Path(args.target).resolve())
