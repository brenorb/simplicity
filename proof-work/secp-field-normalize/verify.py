"""Bind actual multiplication/normalization calls to freshly checked sources."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-wrapper'
sp = importlib.util.spec_from_file_location('normalize_checked_parent', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['Bridge', 'Call']
ROOT = 'FieldNormalize.Call'
FRESH = {'C.jet_sx_zval', 'C.jet_sx_zrep', 'C.jet_secp_fe_math', 'C.jet_secp_fe_nv'}
source_object = v.source_object
loaded_closure = v.loaded_closure


def identity(work):
    parent = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, parent)
    if (not parent['recursive_kernel_check'] or parent['kernel']['exit_code'] != 0 or
            parent['kernel']['log_sha256'] != s.sha((PARENT / 'wrapper-kernel.log').read_bytes()) or
            parent['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked wrapper kernel evidence differs')
    inherited = dict(parent['inherited_extension_sources_objects'])
    inherited.update(parent['extension_sources_objects'])
    dep = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    if (dep['candidate'] != str(work) or set(dep['modules']) != FRESH or
            dep['main_inputs'] != s.input_map() or dep['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('fresh normalizer dependencies differ')
    local = dict(parent['loaded_local_source_objects'])
    for module, row in dep['modules'].items():
        name = module.replace('.', '/') + '.v'
        p = work / 'Coq' / name
        log = work / ('normalize-dependency-' + p.stem + '.log')
        if (name in local or p.is_symlink() or p.read_bytes() != (s.REPO / 'Coq' / name).read_bytes() or
                row['command'] != ['bash', 'build-jets.sh', '--coqc', '-q', str(p)] or
                row['exit_code'] != 0 or row['log_sha256'] != s.sha(log.read_bytes()) or
                {k: row[k] for k in ['source_sha256', 'object_sha256']} != source_object(p)):
            raise ValueError('fresh dependency source/object/compilation differs: ' + module)
        s.safe_source(p.read_text(), module)
        local[name] = source_object(p)
    ext = work / 'normalize'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected normalization source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldNormalize.' + n)
        own.append(('FieldNormalize.' + n, p))
    return own, parent, inherited, local, extra + ['-Q', str(ext), 'FieldNormalize']


def profile(results, definitions, deps):
    six = {ROOT + '.eval_original_field_mul_then_normalize'}
    four = {'FieldNormalize.Bridge.' + n for n in [
        'u64_region_fe_at', 'multiplier_output_fe_at', 'multiplier_second_fe_at',
        'multiplier_output_blocks_distinct', 'fe_at_other_block']}
    if (len(results) != 12 or len(set(results)) != 12 or len(definitions) != 2 or
            not six | four <= set(results) or deps != {
                n: (s.SIX if n in six else s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                    if n in four else set()) for n in results}):
        raise ValueError('normalization profile differs: six closed, five FOUR, one SIX')


def bound(work, r):
    own, parent, inherited, local, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['dependency_receipt_sha256'] != s.sha((HERE / 'DEPENDENCIES.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != local or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('normalization checked-input identity differs')
    profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    return extra


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('compilation already launched; poll original handle')
    own, parent, inherited, local, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
                            'normalize-fresh-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, own, 'normalize', commands, extra)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    actual_local, actual_ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            actual_local != set(local) or actual_ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('normalization loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash,
        dependency_receipt_sha256=s.sha((HERE / 'DEPENDENCIES.json').read_bytes()),
        loaded_local_source_objects=local, inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        actual_multiplication_and_normalization_calls_proved=True,
        normalizer_input_representation_and_bounds_discharged=True,
        canonical_product_limbs_proved=True, second_input_preserved=True,
        outside_original_input_arrays_framed=True, implementation_limb_bounds_explicit=True,
        caller_reader_bounds_discharged=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text()
           for n in ['normalize-assumptions', 'normalize-contracts']}})
    print('12 results freshly compiled: actual multiplier then normalizer, canonical product limbs and framing', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'normalize-kernel', 600)
    log = (work / 'normalize-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
             kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'normalize-kernel.log': log})
    print('Actual multiplier/normalizer calls and canonical product limbs recursively kernel-checked', flush=True)


def check(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    bound(work, r)
    log = (HERE / 'normalize-kernel.log').read_text()
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.encode()) or
            r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((HERE / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes())):
        raise ValueError('normalization kernel evidence differs')
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    local, ext = loaded_closure((HERE / 'loaded-libraries.log').read_text())
    if (local != set(r['loaded_local_source_objects']) or
            ext != set(r['inherited_extension_sources_objects']) | set(r['extension_sources_objects'])):
        raise ValueError('normalization recorded loaded closure differs')
    print('12 normalization results: source/object/parent/driver/kernel identities and exact loaded closure verified', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise ValueError('usage: verify.py compile|kernel|check PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
