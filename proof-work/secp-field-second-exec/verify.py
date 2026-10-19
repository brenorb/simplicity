"""Source-bound original field multiplication through two composed slices."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-checkpoint'
sp = importlib.util.spec_from_file_location('second_checkpoint_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['State', 'Temps', 'Entry', 'Machine', 'Compose']
ROOT = 'FieldSecond.Compose'


def identity(work):
    _, modules, support, extra = v.sources(work)
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    if (r['candidate'] != str(work) or not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'checkpoint-kernel.log').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes()),
                'DISCOVERY.json': s.sha((PARENT / 'DISCOVERY.json').read_bytes())}):
        raise ValueError('checked parent input identity differs')
    v.profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    for n, row in r['loaded_local_source_objects'].items():
        p = work / 'Coq' / n
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('source-bound parent dependency changed: ' + n)
    for m, p in support + modules:
        if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('parent extension source/object changed: ' + m)
    ext = work / 'second'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected second-slice source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldSecond.' + n)
        own.append(('FieldSecond.' + n, p))
    return own, r, extra + ['-Q', str(ext), 'FieldSecond']


def profile(rs, ds, deps):
    six = {'FieldSecond.Machine.exec_second_machine_atomic', 'FieldSecond.Compose.exec_original_through_second'}
    if (len(rs) != 30 or len(set(rs)) != 30 or len(ds) != 27 or not six <= set(rs) or
            deps != {n: (s.SIX if n in six else set()) for n in rs}):
        raise ValueError('exact second-slice profile differs: 28 closed, two SIX')


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    own, parent, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=s.sha((PARENT / 'CHECKED.json').read_bytes()), compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'second-fresh-' + p.stem.lower(), 60)
    rs, ds, deps = g.reports(work, own, 'second', commands, extra)
    profile(rs, ds, deps)
    cmd = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(cmd, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local = {m.replace('.', '/') + '.v' for m in re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    ext = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint|FieldSecond)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    inherited = {m: row for m, row in parent['extension_sources_objects'].items() if m != 'FieldCheckpoint.Columns'}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(parent['loaded_local_source_objects']) or ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('second-slice loaded closure lacks exact source-bound provenance')
    identity(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main inputs or staged work changed')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=s.sha((PARENT / 'CHECKED.json').read_bytes()),
        loaded_local_source_objects=parent['loaded_local_source_objects'], inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: dict(source_sha256=s.sha(p.read_bytes()),
            object_sha256=s.sha(p.with_suffix('.vo').read_bytes())) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())}, original_statement_heads_executed=50,
        slice_entry_memory_and_temporaries_derived=True, compact_machine_observations=True,
        second_slice_integer_no_overflow_proved=False, full_field_product_proved=False,
        public_jet_equivalence=False, normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['second-assumptions', 'second-contracts']}})
    print('30 results compiled: original first fifty statement heads, all boundary facts derived', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    own, parent, extra = identity(work)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        identity(work)
        if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())}):
            raise ValueError('second-slice checked-input identity differs')
        profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
        for m, p in own:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                    object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('second-slice source/object changed: ' + m)
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'second-kernel', 3600)
    log = (work / 'second-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'second-kernel.log': log})
    print('Composed original field execution through fifty statement heads recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
