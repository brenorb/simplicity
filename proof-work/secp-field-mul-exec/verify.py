"""Actual original fe_mul_inner execution; deliberately not a field-value claim."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-shift52'
sp = importlib.util.spec_from_file_location('field_shift_parent', PARENT / 'verify.py')
parent = importlib.util.module_from_spec(sp)
sp.loader.exec_module(parent)
s, g = parent.s, parent.g
ROOT = 'FieldRun.Run'
NAMES = ['Dispatch', 'Run']
NEW = ['C/jet_sx_pure.v', 'C/jet_sx_rep.v', 'C/jet_secp_fns.v', 'C/jet_secp_u128_shift64_oracle.v']


def identity(ext):
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    work = Path(r['candidate'])
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'shift-kernel.log').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('checked shift basis differs')
    inherited, extra = parent.sources(work)
    for name, row in r['loaded_local_source_objects'].items():
        p = work / 'Coq' / name
        if (row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())) or
                p.read_bytes() != (s.REPO / 'Coq' / name).read_bytes()):
            raise ValueError('forced basis differs: ' + name)
    for m, p in inherited:
        if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('proved shift source/object differs: ' + m)
    if ext == work or s.REPO in ext.parents or {p.name for p in ext.glob('*.v')} != {'Dispatch.v', 'Run.v'}:
        raise ValueError('distinct exact field execution namespace required')
    modules = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('field archive/source differs: ' + n)
        s.safe_source(p.read_text(), n)
        modules.append(('FieldRun.' + n, p))
    for n in NEW:
        if (work / 'Coq' / n).is_symlink() or (work / 'Coq' / n).read_bytes() != (s.REPO / 'Coq' / n).read_bytes():
            raise ValueError('additional unchanged dependency differs: ' + n)
    return work, modules, r, extra + ['-Q', str(ext), 'FieldRun']


def profile(results, definitions, deps):
    runtime = {'FieldRun.Dispatch.field_shift_oracle_correct', 'FieldRun.Run.field_table_correct',
               'FieldRun.Run.field_fun_sound', 'FieldRun.Run.eval_field_mul_inner_owned_inplace'}
    closed = {'FieldRun.Run.' + n for n in ['field_mul_completes', 'field_mul_run_eq', 'field_mul_return',
        'field_mul_limbs_length', 'field_cells_rebuild', 'field_mul_out_shape', 'field_mul_out_defined',
        'field_mul_tail', 'field_mul_nonempty', 'field_mul_out_rebuild', 'field_mul_output']}
    defs = {'FieldRun.Dispatch.field_shift_oracle'} | {'FieldRun.Run.' + n for n in
        ['field_table', 'field_mul_regs', 'field_mul_run', 'field_mul_state', 'field_mul_limbs',
         'field_u64_shapes', 'field_cell_value', 'field_cells_defined', 'field_mul_out']}
    expected = {n: (s.SIX if n in runtime else set()) for n in runtime | closed}
    if (len(results) != 15 or set(results) != runtime | closed or len(definitions) != 10 or
            set(definitions) != defs or deps != expected):
        raise ValueError('exact field execution contracts/assumptions differ')


def compile(ext, retry=False):
    if retry:
        prior = json.loads((HERE / 'FIRST-CLOSURE-FAILURE.json').read_text())
        if (HERE / 'RUN.json').exists() or prior['terminal_exit_code'] != 1 or prior['proof_sources_changed']:
            raise ValueError('not the recorded terminal closure failure')
    elif (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    work, modules, basis, extra = identity(ext)
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), external=str(ext),
        checked_parent_sha256=s.sha((PARENT / 'CHECKED.json').read_bytes()), compile_complete=False), indent=2) + '\n'})
    commands = {}
    for n in NEW:
        commands[n] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', n], 'field-fresh-' + Path(n).stem, 180)
    for m, p in modules:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'field-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, modules, 'field', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('field execution library inspection failed')
    loaded = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    extensions = set(re.findall(r'^  ((?:SecpShift|FieldRun)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    inherited = {m: row for m, row in basis['extension_sources_objects'].items() if m != 'SecpShift.Numeric'}
    if (loaded != set(basis['loaded_local_source_objects']) | set(NEW) or len(loaded) != 19 or
            extensions != set(inherited) | {m for m, _ in modules}):
        raise ValueError('loaded closure is not exactly the forced basis plus four fresh sources')
    identity(ext)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('main proof inputs or staging changed')
    record = dict(candidate=str(work), external=str(ext), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_checked_sha256=s.sha((PARENT / 'CHECKED.json').read_bytes()),
        loaded_local_source_objects={n: dict(source_sha256=s.sha((work / 'Coq' / n).read_bytes()),
            object_sha256=s.sha((work / 'Coq' / n).with_suffix('.vo').read_bytes())) for n in sorted(loaded)},
        inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: dict(source_sha256=s.sha(p.read_bytes()),
            object_sha256=s.sha(p.with_suffix('.vo').read_bytes())) for m, p in modules},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        original_c_helper='secp256k1_fe_mul_inner', result_aliases_first_input=True,
        arbitrary_int64_limbs=True, both_regions_owned=True, output_and_second_input_representation=True,
        outside_memory_framing=True, field_product_value_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['field-assumptions', 'field-contracts']}})
    print('Actual original in-place field multiplication execution: 15 results, 19 source-bound local imports', flush=True)


def kernel(ext):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    work, modules, basis, extra = identity(ext)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        identity(ext)
        if (r['external'] != str(ext) or r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
                r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes())):
            raise ValueError('field checked-input identity differs')
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        for n, row in r['loaded_local_source_objects'].items():
            p = work / 'Coq' / n
            if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('field dependency source/object changed: ' + n)
        for m, p in modules:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                    object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('field execution source/object changed: ' + m)
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    policy = s.sha((PARENT / 'kernel-axioms.expected').read_bytes())
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd, kernel_context_sha256=policy,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'field-kernel', 3600)
    log = (work / 'field-kernel.log').read_text()
    if policy != s.sha((PARENT / 'kernel-axioms.expected').read_bytes()):
        raise ValueError('kernel policy changed')
    s.kernel.kernel(log, sorted((PARENT / 'kernel-axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row, kernel_context_sha256=policy,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'field-kernel.log': log})
    print('Original C field-multiplication execution recursively kernel-checked; product value still open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'retry-closure', 'kernel'}:
        raise ValueError('usage: verify.py compile|retry-closure|kernel EXTERNAL_NAMESPACE')
    if sys.argv[1] == 'retry-closure':
        compile(Path(sys.argv[2]).resolve(), retry=True)
    else:
        globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
