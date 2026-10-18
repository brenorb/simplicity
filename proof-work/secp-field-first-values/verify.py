"""Source-bound first original-C checkpoint with derived integer carry bounds."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-checkpoint'
sp = importlib.util.spec_from_file_location('field_values_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
ROOT = 'FieldFirst.Arithmetic'


def identity(work):
    local, modules, support, extra = v.sources(work)
    r = json.loads((PARENT / 'RUN.json').read_text())
    if (r['candidate'] != str(work) or not r['force_rebuilt_entire_local_closure'] or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes()),
                'DISCOVERY.json': s.sha((PARENT / 'DISCOVERY.json').read_bytes())}):
        raise ValueError('source-built parent identity differs')
    for n, row in r['loaded_local_source_objects'].items():
        p = work / 'Coq' / n
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('parent local source/object changed: ' + n)
    for m, p in support + modules:
        if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('parent extension source/object changed: ' + m)
    p = work / 'arith/Arithmetic.v'
    if p.is_symlink() or p.read_bytes() != (HERE / 'Arithmetic.v.source').read_bytes():
        raise ValueError('arithmetic source/archive differs')
    s.safe_source(p.read_text(), ROOT)
    return p, r, extra + ['-Q', str(work / 'arith'), 'FieldFirst']


def profile(results, definitions, deps):
    if (len(results) != 15 or len(set(results)) != 15 or len(definitions) != 3 or
            set(deps) != set(results) or ROOT + '.exec_first_integer_atomic' not in results or
            deps != {n: (s.SIX if n == ROOT + '.exec_first_integer_atomic' else set()) for n in results}):
        raise ValueError('exact 15-result profile differs: fourteen closed, one SIX')


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('arithmetic compile already recorded')
    p, parent, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    commands = {'compile': s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'first-values-compile', 60)}
    rs, ds, deps = g.reports(work, [(ROOT, p)], 'first-values', commands, extra)
    profile(rs, ds, deps)
    cmd = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(cmd, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local = {m.replace('.', '/') + '.v' for m in re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    ext = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint|FieldFirst)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    inherited = {m: row for m, row in parent['extension_sources_objects'].items() if m != 'FieldCheckpoint.Columns'}
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(parent['loaded_local_source_objects']) or ext != set(inherited) | {ROOT}):
        raise ValueError('arithmetic loaded closure differs from source-bound parent')
    identity(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('main inputs or staging changed')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        loaded_local_source_objects=parent['loaded_local_source_objects'], inherited_extension_sources_objects=inherited,
        extension_source_object=dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())),
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        actual_original_prefix_execution=True, prefix_heads=32, implementation_limb_bounds_explicit=True,
        intermediate_no_overflow_and_values_derived=True, caller_reader_bounds_discharged=False,
        all_remaining_stages_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in
            ['first-values-compile', 'first-values-assumptions', 'first-values-contracts']}})
    print('First original C checkpoint integer values/ranges compiled: fourteen closed results, one SIX execution theorem', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    p, parent, extra = identity(work)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        identity(work)
        if (r['parent_compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes()) or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
                r['extension_source_object'] != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))):
            raise ValueError('arithmetic checked-input identity changed')
        profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'first-values-kernel', 3600)
    log = (work / 'first-values-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'first-values-kernel.log': log})
    print('First actual C checkpoint integer values, derived no-overflow and carry bounds recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
