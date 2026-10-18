"""Source-bound actual optional-pegin and full outpoint middle execution."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-outpoint-calls'
sp = importlib.util.spec_from_file_location('outpoint_middle_parent', PARENT / 'verify.py')
calls = importlib.util.module_from_spec(sp)
sp.loader.exec_module(calls)
s, g = calls.s, calls.g
NAMES = ['Common', 'Pegin', 'Middle']
MODULES = ['OutpointMiddle.' + n for n in NAMES]
ROOT = 'OutpointMiddle.Middle'


def profile(results, definitions, deps):
    closed = ['Common.' + n for n in ['op_none_encoding', 'op_some_encoding', 'op_bytes_length',
              'op_outpoint_bytes_length', 'op_outpoint_encoding', 'op_full_bytes_length', 'op_counter_one_then_32']]
    six = ['Common.op_seq_normal_inv', 'Pegin.op_pegin_exec', 'Middle.op_middle_exec', 'Middle.op_middle_then']
    expected = {'OutpointMiddle.' + n: d for ns, d in [(closed, set()), (six, s.SIX)] for n in ns}
    defs = {'OutpointMiddle.Common.' + n for n in ['op_pegin_type', 'op_bytes', 'op_count', 'op_bit',
             'op_overflow', 'op_outpoint_bytes', 'op_full_bytes', 'op_total_count', 'op_middle']}
    if len(results) != 11 or set(results) != set(expected) or set(definitions) != defs or deps != expected:
        raise ValueError('exact eleven-result/nine-definition profile differs: seven closed, four SIX')


def identity(external):
    parent = json.loads((PARENT / 'RUN.json').read_text())
    work, parent_ext = Path(parent['candidate']), Path(parent['external'])
    _, parent_sources, inherited, parent_extra = calls.identity(parent_ext)
    if parent['main_inputs'] != s.input_map() or parent['staged_patch_sha256'] != s.index_hash():
        raise ValueError('parent call-foundation input identity differs')
    if parent['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes())}:
        raise ValueError('parent call-foundation driver differs')
    for m, p in parent_sources:
        row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
        if parent['extension_sources_objects'][m] != row:
            raise ValueError('inherited call source/object differs: ' + m)
        inherited[m] = row
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, parent_ext, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external outpoint middle tree required')
    for m, p in sources:
        if p.is_symlink() or p.read_bytes() != (HERE / (p.name + '.source')).read_bytes():
            raise ValueError('outpoint middle archive differs: ' + m)
        s.safe_source(p.read_text(), m)
    return work, sources, inherited, parent_extra + ['-Q', str(external), 'OutpointMiddle']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('outpoint middle phase compilation already recorded')
    work, sources, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for m, p in sources:
        stem = 'outpoint-middle-' + p.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'outpoint-middle', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('outpoint middle phase library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = json.loads((calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_text())
    if len(local) != 251 or not local <= set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('outpoint middle phase imports lack exact forced-source provenance')
    extensions = set(re.findall(r'^  ((?:OutpointMiddle|OutpointExec|NonceExec|NonceContext)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(MODULES) | set(inherited):
        raise ValueError('unexpected outpoint middle phase extension inventory')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('outpoint middle phase build changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_calls_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        parent_context_checked_sha256=s.sha((calls.phase.PARENT / 'CHECKED.json').read_bytes()),
        parent_source_closure_sha256=s.sha((calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects={n: bound['compiled_and_loaded_local_modules'][n] for n in sorted(local)},
        inherited_extension_sources_objects=inherited, extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_jet_input_bits=1375, phase_input_bits=545,
        memcpy_model_explicit=True, initial_live_context_explicit=True,
        whole_middle_execution_proved=True, whole_jet_execution_proved=False, canonical_option_program=False,
        all_pegin_variants=True, absorbed_byte_counts=[37, 69],
        arbitrary_valid_frames=True, private_source_advance_bits=545,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Complete original outpoint C middle execution compiled; exact eleven-result profile and 251 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('outpoint middle phase kernel already launched; inspect original process')
    work, sources, inherited, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('nonce_local_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, current, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['inherited_extension_sources_objects'] != current or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_calls_compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes()) or
            r['parent_context_checked_sha256'] != s.sha((calls.phase.PARENT / 'CHECKED.json').read_bytes()) or
            r['parent_source_closure_sha256'] != s.sha((calls.phase.context.BASE / 'SOURCE-CLOSURE.json').read_bytes())):
            raise ValueError('outpoint middle phase checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('outpoint middle phase source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'outpoint-middle-kernel', 3600)
    log = (work / 'outpoint-middle-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'outpoint-middle-kernel.log': log})
    print('Complete original outpoint C middle execution recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
