"""Force-build and audit the original-C checkpoint/value-bridge support."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('checkpoint_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('checkpoint_reports', HERE.parent / 'elements-tap-getters/check.py')
NAMES = ['Ops', 'Machine', 'Atomic', 'Prefix', 'Bridge', 'Columns']
ROOTS = ['FieldCheckpoint.Bridge', 'FieldCheckpoint.Columns']


def sources(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('distinct clean audit tree required')
    local = json.loads((HERE / 'DISCOVERY.json').read_text())['local_source_paths']
    if len(local) != 95 or len(set(local)) != 95:
        raise ValueError('unexpected initial local-source inventory')
    for name in local:
        p = work / 'Coq' / name
        if p.is_symlink() or p.read_bytes() != (s.REPO / 'Coq' / name).read_bytes():
            raise ValueError('original main source differs: ' + name)
        s.safe_source(p.read_text(), name)
    modules, support, extra = [], [], []
    for folder, physical, namespace, names in [
        (HERE, 'ext', 'FieldCheckpoint', NAMES),
        (HERE.parent / 'secp-field-shift52', 'shift', 'SecpShift', ['Shift', 'Numeric', 'Rep', 'Oracle']),
        (HERE.parent / 'secp-field-mul-exec', 'field', 'FieldRun', ['Dispatch', 'Run']),
    ]:
        base = work / physical
        if {p.name for p in base.glob('*.v')} != {n + '.v' for n in names}:
            raise ValueError('unexpected extension source inventory: ' + namespace)
        extra += ['-Q', str(base), namespace]
        for n in names:
            p = base / (n + '.v')
            if p.is_symlink() or p.read_bytes() != (folder / (n + '.v.source')).read_bytes():
                raise ValueError('extension/archive mismatch: ' + namespace + '.' + n)
            s.safe_source(p.read_text(), namespace + '.' + n)
            (modules if folder == HERE else support).append((namespace + '.' + n, p))
    if (work / 'Coq/build-jets.sh').read_bytes() != (s.REPO / 'Coq/build-jets.sh').read_bytes():
        raise ValueError('build wrapper changed')
    return local, modules, support, extra


def profile(results, definitions, deps):
    four = {'FieldCheckpoint.Atomic.' + n for n in ['atomic_region', 'atomic_rep', 'atomic_checkpoint']}
    six = {'FieldCheckpoint.Prefix.field_stmt_normal', 'FieldCheckpoint.Prefix.exec_field_first_checkpoint',
           'FieldCheckpoint.Bridge.exec_first_machine_atomic'}
    if len(results) != 41 or len(set(results)) != 41 or len(definitions) != 66:
        raise ValueError('expected exact 41-result/66-definition inventory')
    if set(deps) != set(results) or not four | six <= set(results):
        raise ValueError('missing checkpoint assumption profile')
    classical = s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
    expected = {n: (s.SIX if n in six else classical if n in four else set()) for n in results}
    if deps != expected:
        raise ValueError('checkpoint dependencies differ: 35 closed, three FOUR, three SIX required')


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('build already launched; poll its original handle')
    local, modules, support, extra = sources(work)
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), roots=ROOTS,
        local_sources=95, main_inputs_sha256=s.sha(json.dumps(before, sort_keys=True).encode()),
        staged_patch_sha256=index, compile_complete=False), indent=2) + '\n'})
    flags = []
    cc = Path(s.ENV['COMPCERT'])
    for n in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(cc / n), 'compcert.' + n]
    flags += ['-R', str(cc / 'flocq'), 'Flocq']
    for n in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(cc.parent / 'vst-2.14' / n), 'VST.' + n]
    flags += ['-Q', str(cc.parent / 'vst-2.14/sha'), 'sha']
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-R', 'C', 'C', '-Q', 'Simplicity', 'Simplicity',
        *flags, *local, '-o', 'CheckpointMakefile'], 'checkpoint-makefile', 60)
    print('Force-rebuilding all 95 loaded local sources in a new isolated tree', flush=True)
    commands['build'] = s.run(work, ['make', '-f', 'CheckpointMakefile', '-B', '-j2',
        *(n.removesuffix('.v') + '.vo' for n in local)], 'checkpoint-build', 5400)
    compiled = re.findall(r'^COQC (\S+\.v)$', (work / 'checkpoint-build.log').read_text(), re.M)
    if sorted(compiled) != sorted(local) or len(compiled) != len(set(compiled)):
        raise ValueError('forced compile trace does not cover exactly the loaded local sources')
    bound = {n: dict(source_sha256=s.sha((work / 'Coq' / n).read_bytes()),
        object_sha256=s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes())) for n in local}
    s.changed({HERE / 'BUILD.json': json.dumps(dict(candidate=str(work), command=commands['build'],
        local_source_objects=bound, complete_forced_local_build=True), indent=2) + '\n',
        HERE / 'checkpoint-build.log': (work / 'checkpoint-build.log').read_text()})
    for m, p in support + modules:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
            'checkpoint-fresh-' + m.replace('.', '-'), 90 if p.name == 'Columns.v' else 60)
    results, definitions, deps = g.reports(work, modules, 'checkpoint', commands, extra)
    profile(results, definitions, deps)
    sr, sd, sa = g.reports(work, support, 'checkpoint-support', commands, extra)
    for folder in ['secp-field-shift52', 'secp-field-mul-exec']:
        old = json.loads((HERE.parent / folder / 'CHECKED.json').read_text())
        if (not old['recursive_kernel_check'] or old['kernel']['exit_code'] != 0 or
                set(old['results']) != set(sr) & set(old['results']) or
                any(sa[n] != set(old['dependencies'][n]) for n in old['results']) or
                not set(old['definitions']) <= set(sd)):
            raise ValueError('fresh inherited contracts/assumptions differ: ' + folder)
    cmd = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(cmd, input='Require ' + ' '.join(ROOTS) + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('fresh loaded-library inspection failed')
    actual = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    extensions = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if actual != set(local) or extensions != {m for m, _ in support + modules}:
        raise ValueError('loaded local/extension closure differs from source-built inventory')
    sources(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main inputs or staged work changed')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        inherited_results=sr, inherited_definitions=sd, inherited_dependencies={n: sorted(a) for n, a in sa.items()},
        loaded_local_source_objects=bound, extension_sources_objects={m: dict(source_sha256=s.sha(p.read_bytes()),
            object_sha256=s.sha(p.with_suffix('.vo').read_bytes())) for m, p in support + modules},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes()), 'DISCOVERY.json': s.sha((HERE / 'DISCOVERY.json').read_bytes())},
        force_rebuilt_entire_local_closure=True, prefix_heads=32, actual_original_prefix_execution=True,
        compact_machine_observations=True, cell_and_temp_compression=True, integer_conservation_closed=True,
        all_stage_machine_no_overflow_proved=False, whole_field_product_value_proved=False,
        public_jet_equivalence=False, normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in
            ['checkpoint-assumptions', 'checkpoint-contracts', 'checkpoint-support-assumptions', 'checkpoint-support-contracts']}})
    print('41 checkpoint/reduction results compiled with exact profiles; 95 local imports and six inherited modules rebuilt', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    local, modules, support, extra = sources(work)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        sources(work)
        if (r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or r['candidate'] != str(work) or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes()),
                    'DISCOVERY.json': s.sha((HERE / 'DISCOVERY.json').read_bytes())}):
            raise ValueError('checkpoint checked-input identity differs')
        profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
        for n, row in r['loaded_local_source_objects'].items():
            p = work / 'Coq' / n
            if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('forced local source/object changed: ' + n)
        for m, p in support + modules:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                    object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('extension source/object changed: ' + m)
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + ROOTS)]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'checkpoint-kernel', 3600)
    log = (work / 'checkpoint-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'checkpoint-kernel.log': log})
    print('First actual C checkpoint, atomic bridge and integer conservation recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
