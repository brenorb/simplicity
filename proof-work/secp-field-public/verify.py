"""Exact source-bound audit of the complete original public multiplication function."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-input'
sp = importlib.util.spec_from_file_location('public_checked_input', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['Layout', 'Calls', 'Rest', 'Lifecycle', 'Public']
ROOT = 'FieldPublic.Public'
source_object = v.source_object
loaded_closure = v.loaded_closure


def identity(work):
    parent = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, parent)
    if (not parent['recursive_kernel_check'] or parent['kernel']['exit_code'] != 0 or
            parent['kernel']['log_sha256'] != s.sha((PARENT / 'input-kernel.log').read_bytes()) or
            parent['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked input-chain kernel evidence differs')
    dep = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    expected = {'C.jet_frame_copy', 'C.jet_frame_copy_layout'}
    if (dep['candidate'] != str(work) or set(dep['modules']) != expected or
            dep['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            dep['main_inputs'] != s.input_map() or dep['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('public copy dependency receipt differs')
    local = dict(parent['loaded_local_source_objects'])
    for module, row in dep['modules'].items():
        name = module.replace('.', '/') + '.v'
        p = work / 'Coq' / name
        if (name in local or p.is_symlink() or p.read_bytes() != (s.REPO / 'Coq' / name).read_bytes() or
                row['command'] != ['bash', 'build-jets.sh', '--coqc', '-q', str(p)] or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((work / ('public-dependency-' + module + '.log')).read_bytes()) or
                {k: row[k] for k in ['source_sha256', 'object_sha256']} != source_object(p)):
            raise ValueError('public copy dependency source/object/compilation differs: ' + module)
        s.safe_source(p.read_text(), module)
        local[name] = source_object(p)
    inherited = dict(parent['inherited_extension_sources_objects'])
    inherited.update(parent['extension_sources_objects'])
    ext = work / 'public'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected public-function source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('public-function archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldPublic.' + n)
        own.append(('FieldPublic.' + n, p))
    return own, parent, inherited, local, extra + ['-Q', str(ext), 'FieldPublic']


def profile(results, definitions, deps):
    six = {'FieldPublic.Layout.exec_public_copy',
        'FieldPublic.Calls.exec_read_call', 'FieldPublic.Calls.exec_mul_call',
        'FieldPublic.Calls.exec_write_call', 'FieldPublic.Calls.exec_four_call_body',
        'FieldPublic.Rest.exec_original_public_rest', 'FieldPublic.Lifecycle.prepare_three',
        ROOT + '.eval_original_public_field_multiply'}
    four = {'FieldPublic.Lifecycle.allocated_frame', 'FieldPublic.Lifecycle.free_three'}
    if (len(results) != 16 or len(set(results)) != 16 or len(definitions) != 10 or
            not six | four <= set(results) or deps != {
                n: (s.SIX if n in six else s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                    if n in four else set()) for n in results}):
        raise ValueError('public-function profile differs: six closed, two FOUR, eight SIX')


def bound(work, r):
    own, parent, inherited, local, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['dependency_receipt_sha256'] != s.sha((HERE / 'DEPENDENCIES.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != local or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('public-function checked-input identity differs')
    profile(r['results'], r['definitions'], {n: set(a) for n, a in r['dependencies'].items()})
    return extra


def negative_checks(r, loaded):
    deps = {n: set(a) for n, a in r['dependencies'].items()}
    bad = {n: set(a) for n, a in deps.items()}
    bad[r['results'][0]].add('Unreviewed.extra_assumption')
    try:
        profile(r['results'], r['definitions'], bad)
    except ValueError:
        pass
    else:
        raise ValueError('extra assumption was accepted')
    local, ext = loaded_closure(loaded)
    if (local != set(r['loaded_local_source_objects']) or
            ext != set(r['inherited_extension_sources_objects']) | set(r['extension_sources_objects'])):
        raise ValueError('public-function recorded loaded closure differs')
    if loaded_closure(loaded + '\n  Unreviewed.Unknown\n')[1] == ext:
        raise ValueError('unfamiliar namespace disappeared from loaded inventory')
    return 'Extra assumption rejected; unfamiliar module detected; exact positive loaded closure matched.\n'


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('public-function compilation already launched; poll original handle')
    own, parent, inherited, local, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
                            'public-fresh-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, own, 'public', commands, extra)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    actual_local, actual_ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            actual_local != set(local) or actual_ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('public-function loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash,
        dependency_receipt_sha256=s.sha((HERE / 'DEPENDENCIES.json').read_bytes()),
        loaded_local_source_objects=local, inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        actual_public_function_call_proved=True, full_word256_pair_input_domain=True,
        caller_reader_bounds_discharged=True, multiplier_initial_representation_discharged=True,
        encoded_input_product_and_output_frame_proved=True, boolean_return_conversion_proved=True,
        actual_three_allocations_source_copy_and_frees_proved=True,
        literal_simplicity_program_composed=False, public_caller_lifecycle_proved=True,
        public_jet_equivalence=False, normal_registration=False, coverage_added=0,
        recursive_kernel_check=False)
    tests = negative_checks(r, query.stdout)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'negative-checks.log': tests,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['public-assumptions', 'public-contracts']}})
    print('16 public-function results freshly audited: actual entry, copy, complete body, boolean return and three frees', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('public-function kernel check already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'public-kernel', 600)
    log = (work / 'public-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'public-kernel.log': log})
    print('Complete original public multiplication function recursively kernel-checked', flush=True)


def check(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    bound(work, r)
    log = (HERE / 'public-kernel.log').read_text()
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.encode()) or
            r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((HERE / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes())):
        raise ValueError('public-function kernel evidence differs')
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    negative_checks(r, (HERE / 'loaded-libraries.log').read_text())
    print('16 public-function results: exact source/object/parent/driver/kernel identities and loaded closure verified', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise ValueError('usage: verify.py compile|kernel|check PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
