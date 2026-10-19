"""Exact source-bound audit of the full-input reader/multiplier/writer chain."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'secp-field-writer'
sp = importlib.util.spec_from_file_location('input_checked_writer', PARENT / 'verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, g = v.s, v.g
NAMES = ['Input', 'Reader', 'Pair', 'Compose']
ROOT = 'FieldInput.Compose'
source_object = v.source_object
loaded_closure = v.loaded_closure


def identity(work):
    parent = json.loads((PARENT / 'CHECKED.json').read_text())
    extra = v.bound(work, parent)
    if (not parent['recursive_kernel_check'] or parent['kernel']['exit_code'] != 0 or
            parent['kernel']['log_sha256'] != s.sha((PARENT / 'writer-kernel.log').read_bytes()) or
            parent['kernel_launch_sha256'] != s.sha((PARENT / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((PARENT / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes())):
        raise ValueError('checked writer kernel evidence differs')
    dep = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    if (dep['candidate'] != str(work) or set(dep['modules']) != {'C.jet_secp_local_call'} or
            dep['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            dep['main_inputs'] != s.input_map() or dep['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('reader-call dependency receipt differs')
    p = work / 'Coq/C/jet_secp_local_call.v'
    row = dep['modules']['C.jet_secp_local_call']
    if (p.is_symlink() or p.read_bytes() != (s.REPO / 'Coq/C/jet_secp_local_call.v').read_bytes() or
            row['command'] != ['bash', 'build-jets.sh', '--coqc', '-q', str(p)] or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / 'input-dependency-local-call.log').read_bytes()) or
            {k: row[k] for k in ['source_sha256', 'object_sha256']} != source_object(p)):
        raise ValueError('reader-call dependency source/object/compilation differs')
    s.safe_source(p.read_text(), 'C.jet_secp_local_call')
    local = dict(parent['loaded_local_source_objects'])
    if 'C/jet_secp_local_call.v' in local:
        raise ValueError('reader-call dependency was not an additional fresh module')
    local['C/jet_secp_local_call.v'] = source_object(p)
    inherited = dict(parent['inherited_extension_sources_objects'])
    inherited.update(parent['extension_sources_objects'])
    ext = work / 'input'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected full-input source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('full-input archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldInput.' + n)
        own.append(('FieldInput.' + n, p))
    return own, parent, inherited, local, extra + ['-Q', str(ext), 'FieldInput']


def profile(results, definitions, deps):
    six = {'FieldInput.Reader.eval_read_fe_with_cursor', 'FieldInput.Pair.eval_read_field_pair',
           ROOT + '.eval_original_read_pair_mul_write'}
    four = {'FieldInput.Input.owned_field_region', 'FieldInput.Input.pair_initial_rep',
        'FieldInput.Reader.pair_input_windows', 'FieldInput.Reader.local_read_final_cursor',
        'FieldInput.Reader.reader_preserves_other', ROOT + '.frame_fields_on_unchanged_block'}
    if (len(results) != 22 or len(set(results)) != 22 or len(definitions) != 4 or
            not six | four <= set(results) or deps != {
                n: (s.SIX if n in six else s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                    if n in four else set()) for n in results}):
        raise ValueError('full-input profile differs: 13 closed, six FOUR, three SIX')


def bound(work, r):
    own, parent, inherited, local, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['dependency_receipt_sha256'] != s.sha((HERE / 'DEPENDENCIES.json').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != local or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('full-input checked-input identity differs')
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
        raise ValueError('full-input recorded loaded closure differs')
    if loaded_closure(loaded + '\n  Unreviewed.Unknown\n')[1] == ext:
        raise ValueError('unfamiliar namespace disappeared from loaded inventory')
    return 'Extra assumption rejected; unfamiliar module detected; exact positive loaded closure matched.\n'


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('full-input compilation already launched; poll original handle')
    own, parent, inherited, local, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
                            'input-fresh-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, own, 'input', commands, extra)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    actual_local, actual_ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            actual_local != set(local) or actual_ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('full-input loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash,
        dependency_receipt_sha256=s.sha((HERE / 'DEPENDENCIES.json').read_bytes()),
        loaded_local_source_objects=local, inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        actual_two_readers_multiplier_writer_proved=True, full_word256_pair_input_domain=True,
        caller_reader_bounds_discharged=True, multiplier_initial_representation_discharged=True,
        source_cursor_advanced_by_512=True, encoded_input_product_and_output_frame_proved=True,
        all_three_caller_locals_freeable_for_cleanup=True,
        literal_simplicity_program_composed=False, public_caller_lifecycle_proved=False,
        public_jet_equivalence=False, normal_registration=False, coverage_added=0,
        recursive_kernel_check=False)
    tests = negative_checks(r, query.stdout)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'negative-checks.log': tests,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['input-assumptions', 'input-contracts']}})
    print('22 full-input results freshly audited: two original readers, multiplier, writer, cursor and all cleanup storage', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('full-input kernel check already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'input-kernel', 600)
    log = (work / 'input-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'input-kernel.log': log})
    print('Full-input original two-reader/multiplier/writer composition recursively kernel-checked', flush=True)


def check(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    bound(work, r)
    log = (HERE / 'input-kernel.log').read_text()
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.encode()) or
            r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((HERE / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes())):
        raise ValueError('full-input kernel evidence differs')
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    negative_checks(r, (HERE / 'loaded-libraries.log').read_text())
    print('22 full-input results: exact source/object/parent/driver/kernel identities and loaded closure verified', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise ValueError('usage: verify.py compile|kernel|check PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
