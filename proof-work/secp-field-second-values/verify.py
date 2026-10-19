"""Source-bound integer bridge for the composed second original-C checkpoint."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SECOND = HERE.parent / 'secp-field-second-exec'
FIRST = HERE.parent / 'secp-field-first-values'
sp = importlib.util.spec_from_file_location('second_values_execution', SECOND / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
f = s.load('second_values_first', FIRST / 'verify.py')
NAMES = ['Accum', 'Arithmetic']
ROOT = 'FieldSecondValues.Arithmetic'


def checked(folder, work):
    r = json.loads((folder / 'CHECKED.json').read_text())
    log = folder / ('second-kernel.log' if folder == SECOND else 'first-values-kernel.log')
    if (r['candidate'] != str(work) or not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['tools_sha256'] != {'verify.py': s.sha((folder / 'verify.py').read_bytes())}):
        raise ValueError('checked parent identity differs: ' + str(folder))
    return r


def source_object(p):
    return dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))


def identity(work):
    second, base, extra = v.identity(work)
    pfirst, first_base, _ = f.identity(work)
    rsecond, rfirst = checked(SECOND, work), checked(FIRST, work)
    v.profile(rsecond['results'], rsecond['definitions'], {n: set(a) for n, a in rsecond['dependencies'].items()})
    f.profile(rfirst['results'], rfirst['definitions'], {n: set(a) for n, a in rfirst['dependencies'].items()})
    inherited = {m: row for m, row in base['extension_sources_objects'].items() if m != 'FieldCheckpoint.Columns'}
    if (rsecond['parent_checked_sha256'] != s.sha((v.PARENT / 'CHECKED.json').read_bytes()) or
            rfirst['parent_compile_sha256'] != s.sha((f.PARENT / 'RUN.json').read_bytes()) or
            rsecond['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            rfirst['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            first_base['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            rsecond['inherited_extension_sources_objects'] != inherited or
            rfirst['inherited_extension_sources_objects'] != inherited):
        raise ValueError('parents do not bind the same source-built closure')
    for m, p in second:
        if rsecond['extension_sources_objects'][m] != source_object(p):
            raise ValueError('checked second execution source/object changed: ' + m)
        inherited[m] = source_object(p)
    if rfirst['extension_source_object'] != source_object(pfirst):
        raise ValueError('checked first integer source/object changed')
    inherited['FieldFirst.Arithmetic'] = source_object(pfirst)
    ext = work / 'second-values'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected second integer source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldSecondValues.' + n)
        own.append(('FieldSecondValues.' + n, p))
    return own, base, inherited, extra + ['-Q', str(work / 'arith'), 'FieldFirst', '-Q', str(ext), 'FieldSecondValues']


def parent_hashes():
    return {n: s.sha((p / 'CHECKED.json').read_bytes()) for n, p in [('second-exec', SECOND), ('first-values', FIRST)]}


def profile(rs, ds, deps):
    endpoint = ROOT + '.exec_original_second_integer_atomic'
    if (len(rs) != 25 or len(set(rs)) != 25 or len(ds) != 10 or endpoint not in rs or
            deps != {n: (s.SIX if n == endpoint else set()) for n in rs}):
        raise ValueError('exact second integer profile differs: 24 closed, one SIX')


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    own, base, inherited, extra = identity(work)
    before, index, parents = s.input_map(), s.index_hash(), parent_hashes()
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parents, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'second-values-fresh-' + p.stem.lower(), 60)
    rs, ds, deps = g.reports(work, own, 'second-values', commands, extra)
    profile(rs, ds, deps)
    cmd = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(cmd, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local = {m.replace('.', '/') + '.v' for m in re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    ext = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint|FieldFirst|FieldSecond|FieldSecondValues)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(base['loaded_local_source_objects']) or ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('second integer loaded closure lacks exact source-built provenance')
    identity(work)
    if s.input_map() != before or s.index_hash() != index or parents != parent_hashes():
        raise ValueError('main inputs, staging or parent evidence changed')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parents, loaded_local_source_objects=base['loaded_local_source_objects'],
        inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())}, original_statement_heads_executed=50,
        slice_entry_memory_and_temporaries_derived=True, second_slice_integer_no_overflow_proved=True,
        implementation_limb_bounds_explicit=True, caller_reader_bounds_discharged=False,
        full_field_product_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['second-values-assumptions', 'second-values-contracts']}})
    print('25 results freshly compiled: composed original C second checkpoint with derived integer values and bounds', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    own, base, inherited, extra = identity(work)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        identity(work)
        if (r['parent_checked_sha256'] != parent_hashes() or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
                r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
                r['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
                r['inherited_extension_sources_objects'] != inherited or
                r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
            raise ValueError('second integer checked-input identity differs')
        profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'second-values-kernel', 3600)
    log = (work / 'second-values-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'second-values-kernel.log': log})
    print('Composed original C second checkpoint integer values, non-overflow and split bounds recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
