"""Exact source/object/assumption/kernel audit of real multiplication and writing."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('writer_fresh_dependencies', HERE / 'dependencies.py')
d = importlib.util.module_from_spec(sp)
sp.loader.exec_module(d)
s, g = d.s, d.g
NAMES = ['Bridge', 'Call']
ROOT = 'FieldWriter.Call'
source_object = d.v.source_object
loaded_closure = d.v.loaded_closure


def identity(work):
    dep = json.loads((HERE / 'DEPENDENCIES.json').read_text())
    parent, extra, local = d.bound(work, dep)
    inherited = dict(parent['inherited_extension_sources_objects'])
    inherited.update(parent['extension_sources_objects'])
    del inherited['FieldNormalize.Call']  # Separate normalizer endpoint not loaded here.
    ext = work / 'writer'
    if {p.name for p in ext.glob('*.v')} != {n + '.v' for n in NAMES}:
        raise ValueError('unexpected multiplication/writer source inventory')
    own = []
    for n in NAMES:
        p = ext / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / (n + '.v.source')).read_bytes():
            raise ValueError('writer archive/source mismatch: ' + n)
        s.safe_source(p.read_text(), 'FieldWriter.' + n)
        own.append(('FieldWriter.' + n, p))
    reused = [('C.jet_secp_write_fe_wide_' + n, work / 'Coq/C' / ('jet_secp_write_fe_wide_' + n + '.v'))
              for n in ['checks', 'values', 'exec']]
    return own, reused, parent, inherited, local, extra + ['-Q', str(ext), 'FieldWriter']


def profile(results, definitions, deps):
    six = {ROOT + '.eval_original_field_mul_then_write',
           'C.jet_secp_write_fe_wide_exec.eval_local_wide_write_fe'}
    four = {'FieldWriter.Bridge.' + n for n in ['wide_initial_from_owned_words',
        'multiplier_output_storage', 'multiplier_second_storage', 'multiplier_writer_rep',
        'fe_at_on_unchanged_block']}
    if (len(results) != 26 or len(set(results)) != 26 or len(definitions) != 7 or
            not six | four <= set(results) or deps != {
                n: (s.SIX if n in six else s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                    if n in four else set()) for n in results}):
        raise ValueError('writer profile differs: 19 closed, five FOUR, two SIX')


def bound(work, r):
    own, reused, parent, inherited, local, extra = identity(work)
    if (r['parent_checked_sha256'] != s.sha((d.PARENT / 'CHECKED.json').read_bytes()) or
            r['dependency_receipt_sha256'] != s.sha((HERE / 'DEPENDENCIES.json').read_bytes()) or
            r['tools_sha256'] != {n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'dependencies.py']} or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != local or
            r['inherited_extension_sources_objects'] != inherited or
            r['extension_sources_objects'] != {m: source_object(p) for m, p in own}):
        raise ValueError('multiplication/writer checked-input identity differs')
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
        raise ValueError('recorded writer loaded closure differs')
    if loaded_closure(loaded + '\n  Unreviewed.Unknown\n')[1] == ext:
        raise ValueError('unfamiliar module disappeared from closure inventory')
    return 'Extra assumption rejected; unfamiliar module detected; exact positive loaded closure matched.\n'


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('writer compilation already launched; poll original handle')
    own, reused, parent, inherited, local, extra = identity(work)
    before, index = s.input_map(), s.index_hash()
    parent_hash = s.sha((d.PARENT / 'CHECKED.json').read_bytes())
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), root=ROOT,
        parent_checked_sha256=parent_hash, compile_complete=False), indent=2) + '\n'})
    commands = {}
    for m, p in own:
        commands[m] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)],
                            'writer-fresh-' + p.stem.lower(), 60)
    results, definitions, deps = g.reports(work, reused + own, 'writer', commands, extra)
    profile(results, definitions, deps)
    query = subprocess.run(['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra],
        input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq', env=s.ENV,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    actual_local, actual_ext = loaded_closure(query.stdout)
    if (query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout) or
            actual_local != set(local) or actual_ext != set(inherited) | {m for m, _ in own}):
        raise ValueError('writer loaded closure lacks exact source-built provenance')
    r = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, dependencies={n: sorted(a) for n, a in deps.items()},
        parent_checked_sha256=parent_hash,
        dependency_receipt_sha256=s.sha((HERE / 'DEPENDENCIES.json').read_bytes()),
        loaded_local_source_objects=local, inherited_extension_sources_objects=inherited,
        extension_sources_objects={m: source_object(p) for m, p in own},
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'dependencies.py']},
        fresh_additional_local_sources=49, reused_writer_results=16, new_composition_results=10,
        actual_multiplication_and_writer_calls_proved=True,
        writer_bounds_representation_and_frame_invariant_discharged=True,
        encoded_product_and_output_frame_proved=True, second_input_preserved=True,
        both_caller_fields_freeable_for_cleanup=True,
        implementation_limb_bounds_explicit=True, caller_reader_bounds_discharged=False,
        literal_simplicity_program_composed=False, public_jet_equivalence=False,
        normal_registration=False, coverage_added=0, recursive_kernel_check=False)
    tests = negative_checks(r, query.stdout)
    bound(work, r)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        HERE / 'negative-checks.log': tests,
        **{HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in ['writer-assumptions', 'writer-contracts']}})
    print('26 results freshly audited: real multiplier and writer, encoded product, output frame, second input, both fields freeable', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('writer kernel check already launched; poll original handle')
    r = json.loads((HERE / 'RUN.json').read_text())
    extra = bound(work, r)
    cmd = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=cmd,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, cmd, 'writer-kernel', 600)
    log = (work / 'writer-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound(work, r)
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'writer-kernel.log': log})
    print('Real original multiplier and writer composition recursively kernel-checked', flush=True)


def check(work):
    r = json.loads((HERE / 'CHECKED.json').read_text())
    bound(work, r)
    log = (HERE / 'writer-kernel.log').read_text()
    if (not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0 or
            r['kernel']['log_sha256'] != s.sha(log.encode()) or
            r['kernel_launch_sha256'] != s.sha((HERE / 'KERNEL-RUN.json').read_bytes()) or
            json.loads((HERE / 'KERNEL-RUN.json').read_text())['compile_sha256'] != s.sha((HERE / 'RUN.json').read_bytes())):
        raise ValueError('writer kernel evidence differs')
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    negative_checks(r, (HERE / 'loaded-libraries.log').read_text())
    print('26 writer/composition results: exact source/object/parent/driver/kernel identities and loaded closure verified', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in {'compile', 'kernel', 'check'}:
        raise ValueError('usage: verify.py compile|kernel|check PRIVATE_AUDIT_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
