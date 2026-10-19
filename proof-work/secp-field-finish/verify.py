"""Source-bound original field multiplier complete body and output-product modulo relation."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-fifth'
sp = importlib.util.spec_from_file_location('finish_checkpoint_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['State', 'Values', 'Word', 'Execute', 'Arithmetic', 'Product']
ROOT = 'FieldFinish.Product'


def source_object(p):
    return dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))


def loaded_closure(output):
    loaded = set(re.findall(r'^  ([A-Za-z_][A-Za-z0-9_.]+)$', output, re.M))
    local_roots = {'C', 'Simplicity', 'Util'}
    trusted_roots = {'Coq', 'compcert', 'Flocq', 'VST', 'sha'}
    local = {m.replace('.', '/') + '.v' for m in loaded if m.split('.')[0] in local_roots}
    # Inventory every non-standard module, including unfamiliar namespaces.
    # An unexpected namespace must fail exact provenance comparison, not vanish
    # through a hardcoded list of all previous checkpoint namespace names.
    extensions = {m for m in loaded if m.split('.')[0] not in local_roots | trusted_roots}
    return local, extensions


def identity(work):
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, r)
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha((PARENT / 'fifth-kernel.log').read_bytes()) or
            r['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked fifth-checkpoint kernel evidence differs')
    inherited = dict(r['inherited_extension_sources_objects'])
    inherited.update(r['extension_sources_objects'])
    columns_parent = HERE.parent / 'secp-field-checkpoint'
    columns = json.loads((columns_parent / 'CHECKED.json').read_text())
    cp = work / 'ext/Columns.v'
    if (not columns['recursive_kernel_check'] or columns['kernel']['exit_code'] != 0 or
            columns['kernel']['log_sha256'] != s.sha((columns_parent / 'checkpoint-kernel.log').read_bytes()) or
            columns['candidate'] != str(work) or
            cp.read_bytes() != (columns_parent / 'Columns.v.source').read_bytes() or
            columns['extension_sources_objects']['FieldCheckpoint.Columns'] != source_object(cp)):
        raise ValueError('checked integer-conservation source/object evidence differs')
    inherited['FieldCheckpoint.Columns'] = source_object(cp)
    ext = work / 'finish'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected finish-slice source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldFinish.' + n)
        own.append(('FieldFinish.' + n, p))
    return own, r, inherited, extra + ['-Q', str(ext), 'FieldFinish']


def profile(rs, ds, deps):
    six = {'FieldFinish.Execute.exec_finish_checkpoint', 'FieldFinish.Execute.exec_original_field_body',
           'FieldFinish.Arithmetic.exec_original_field_body_integer', ROOT + '.exec_original_field_body_product'}
    four = {'FieldFinish.Execute.finish_checkpoint_rep', 'FieldFinish.Execute.checkpoint_output_words'}
    if (len(rs) != 48 or len(set(rs)) != 48 or len(ds) != 29 or not six | four <= set(rs) or
            deps != {n: (s.SIX if n in six else s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'} if n in four else set()) for n in rs}):
        raise ValueError('exact finish-slice profile differs: 42 closed, two FOUR, four SIX')


def bound(work, r):
    own, parent, inherited, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != parent['loaded_local_source_objects'] or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('finish-slice checked-input identity differs')
    profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    return extra


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    own, parent, inherited, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], 'finish-fresh-' + p.stem.lower(), 60)
    rs, ds, deps = g.reports(work, own, 'finish', commands, extra)
    profile(rs, ds, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    local, ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            local != set(parent['loaded_local_source_objects']) or ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('finish-slice loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=rs, definitions=ds, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash, loaded_local_source_objects=parent['loaded_local_source_objects'],
        inherited_extension_sources_objects=inherited, extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())}, original_statement_heads_executed=107, original_final_statement_executed=True,
        checkpoint_entry_derived=True, last_two_aliased_output_stores_executed=True, first_three_outputs_preserved=True,
        updated_reusable_checkpoint_returned=True, finish_slice_integer_no_overflow_proved=True,
        implementation_limb_bounds_explicit=True, caller_reader_bounds_discharged=False,
        full_field_product_modulo_proved=True, complete_function_call_proved=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['finish-assumptions', 'finish-contracts']}})
    print('48 results freshly compiled: complete original multiplier body and exact product modulo the field prime', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'finish-kernel', 3600)
    log = (work / 'finish-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'finish-kernel.log': log})
    print('Complete original C multiplier body and its output-product modulo relation recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel'}:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
