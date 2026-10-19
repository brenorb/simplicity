"""Source-bound actual field multiplication through its first output store."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-second-values'
sp = importlib.util.spec_from_file_location('third_checkpoint_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['State', 'Entry', 'Values', 'Machine', 'Compose', 'Arithmetic']
ROOT = 'FieldThird.Arithmetic'


def identity(work):
    previous, base, inherited, extra = v.identity(work)
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    if (r['candidate'] != str(work) or not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'second-values-kernel.log').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['parent_checked_sha256'] != v.parent_hashes() or
            r['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())} or
            r['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
            r['inherited_extension_sources_objects'] != inherited):
        raise ValueError('checked second-integer parent identity differs')
    v.profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    for m, p in previous:
        if r['extension_sources_objects'][m] != v.source_object(p):
            raise ValueError('parent extension source/object changed: ' + m)
        inherited[m] = v.source_object(p)
    ext = work / 'third'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected third-slice source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldThird.' + n)
        own.append(('FieldThird.' + n, p))
    return own, base, inherited, extra + ['-Q', str(ext), 'FieldThird']


def profile(rs, ds, deps):
    six = {'FieldThird.Machine.exec_third_machine_atomic', 'FieldThird.Compose.exec_original_through_third',
           ROOT + '.exec_original_third_integer_atomic'}
    if (len(rs) != 49 or len(set(rs)) != 49 or len(ds) != 39 or not six <= set(rs) or
            deps != {n: (s.SIX if n in six else set()) for n in rs}):
        raise ValueError('exact third-slice profile differs: 46 closed, three SIX')


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    own, base, inherited, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'third-fresh-' + p.stem.lower(), 60)
    rs, ds, deps = g.reports(work, own, 'third', commands, extra)
    profile(rs, ds, deps)
    cmd = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(cmd, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local = {m.replace('.', '/') + '.v' for m in re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    ext = set(re.findall(r'^  ((?:SecpShift|FieldRun|FieldCheckpoint|FieldFirst|FieldSecond|FieldSecondValues|FieldThird)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(base['loaded_local_source_objects']) or ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('third-slice loaded closure lacks exact source-built provenance')
    identity(work)
    if (s.input_map() != before or s.index_hash() != index or
            s.sha((PARENT / 'CHECKED.json').read_bytes()) != parent_hash):
        raise ValueError('main inputs, staging or parent evidence changed')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash, loaded_local_source_objects=base['loaded_local_source_objects'],
        inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: v.source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())}, original_statement_heads_executed=68,
        slice_entry_memory_and_temporaries_derived=True, first_aliased_output_store_executed=True,
        original_cached_a0_preserved=True, third_slice_integer_no_overflow_proved=True,
        implementation_limb_bounds_explicit=True, caller_reader_bounds_discharged=False,
        full_field_product_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['third-assumptions', 'third-contracts']}})
    print('49 results freshly compiled: original C through first aliased output store, integer values and derived carry bounds', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    own, base, inherited, extra = identity(work)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        identity(work)
        if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
                r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
                r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
                r['loaded_local_source_objects'] != base['loaded_local_source_objects'] or
                r['inherited_extension_sources_objects'] != inherited or
                r['extension_sources_objects'] != {m: v.source_object(p) for m, p in own}):
            raise ValueError('third-slice checked-input identity differs')
        profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    bound()
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'third-kernel', 3600)
    log = (work / 'third-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'third-kernel.log': log})
    print('Original C first output store and its integer/carry bounds recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
