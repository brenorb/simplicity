"""Source-bound checks of the original nonce-processing C phase."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-nonce-context'
sp = importlib.util.spec_from_file_location('nonce_phase_context', PARENT / 'verify.py')
context = importlib.util.module_from_spec(sp)
sp.loader.exec_module(context)
s, g = context.s, context.g
NAMES = ['Effects', 'Calls', 'Prefix', 'Payload', 'Phase']
MODULES = ['NonceExec.' + n for n in NAMES]
ROOT = 'NonceExec.Phase'


def profile(results, definitions, deps):
    closed = ['Calls.' + n for n in ['nonce_local_frame_base', 'nonce_readbit_link', 'nonce_forward_link',
              'nonce_uchar_link', 'nonce_bit_bool']]
    closed += ['Payload.nonce_readbytes_link', 'Payload.nonce_uchars_link', 'Phase.nonce_counter_one_then_32']
    four = ['Effects.' + n for n in ['nonce_effects_refl', 'nonce_effects_mono', 'nonce_effects_trans',
            'nonce_effects_access', 'nonce_effects_union', 'nonce_effects_fields', 'nonce_effects_input',
            'nonce_ctx_other', 'nonce_effects_ctx']]
    four += ['Prefix.nonce_cells_head', 'Prefix.nonce_cells_tail']
    six = ['Calls.nonce_read_bit', 'Calls.nonce_forward_one', 'Calls.nonce_add_byte', 'Prefix.nonce_read_cell',
           'Prefix.nonce_explicit_prefix', 'Prefix.nonce_confidential_prefix', 'Payload.nonce_payload_exec',
           'Phase.nonce_present_prefix', 'Phase.nonce_phase_exec']
    expected = {'NonceExec.' + n: d for ns, d in [(closed, set()), (four, context.base.FOUR), (six, s.SIX)] for n in ns}
    defs = {'NonceExec.Effects.nonce_effects'} | {'NonceExec.Phase.' + n for n in
            ['nonce_present_temps', 'nonce_phase_temps', 'nonce_phase_count', 'nonce_phase_read_bits', 'nonce_phase_overflow']}
    if len(results) != 28 or set(results) != set(expected) or set(definitions) != defs or deps != expected:
        raise ValueError('exact 28-result/6-definition profile differs: eight closed, eleven FOUR, nine SIX')


def identity(external):
    r = json.loads((PARENT / 'CHECKED.json').read_text())
    work, parent_ext = Path(r['candidate']), Path(r['external'])
    if not r['recursive_kernel_check'] or r['kernel']['exit_code'] != 0:
        raise ValueError('completed nonce program/body/entry kernel check required')
    context.identity(parent_ext)
    for m, row in r['extension_sources_objects'].items():
        p = parent_ext / (m.rsplit('.', 1)[1] + '.v')
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('inherited nonce source/object changed: ' + m)
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, parent_ext, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external phase tree required')
    for m, p in sources:
        if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
            raise ValueError('nonce phase archive differs: ' + m)
        s.safe_source(p.read_text(), m)
    return work, sources, r, ['-Q', str(parent_ext), 'NonceContext', '-Q', str(external), 'NonceExec']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('nonce phase compilation already recorded')
    work, sources, parent, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for m, p in sources:
        stem = 'nonce-phase-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'nonce-phase', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('nonce phase library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((context.BASE / 'SOURCE-CLOSURE.json').read_text())
    if len(local) != 251 or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('nonce phase imports lack exact forced-source provenance')
    extensions = set(re.findall(r'^  ((?:NonceExec|NonceContext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(MODULES) | set(parent['extension_sources_objects']):
        raise ValueError('unexpected nonce phase extension inventory')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('nonce phase build changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_checked_sha256=s.sha((PARENT / 'CHECKED.json').read_bytes()),
        parent_source_closure_sha256=s.sha((context.BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        inherited_extension_sources_objects=parent['extension_sources_objects'], extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', memcpy_model_explicit=True, nonce_phase_execution_proved=True,
        initial_live_context_explicit=True, whole_jet_execution_proved=False,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Complete nonce-processing C phase compiled; exact 28-result profile and 251 source-bound imports verified', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('nonce phase kernel already launched; inspect original process')
    work, sources, parent, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('nonce_phase_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, current_parent, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or
            r['inherited_extension_sources_objects'] != current_parent['extension_sources_objects'] or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_checked_sha256'] != s.sha((PARENT / 'CHECKED.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((context.BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('nonce phase checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('nonce phase source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'nonce-phase-kernel', 3600)
    log = (work / 'nonce-phase-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'nonce-phase-kernel.log': log})
    print('Complete original nonce-processing C phase recursively kernel-checked; enclosing jet remains open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
