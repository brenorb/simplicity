"""Every outpoint input executes from actual initialization, with constructed frames."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / 'elements-outpoint-local'
START = HERE.parent / 'elements-entropy-ready'
sp = importlib.util.spec_from_file_location('outpoint_ready_parent', PARENT / 'verify.py')
local = importlib.util.module_from_spec(sp)
sp.loader.exec_module(local)
s, g = local.s, local.g
ROOT = 'OutpointReady.Ready'


def profile(results, definitions, deps):
    expected = {ROOT + '.' + n: s.SIX for n in ['outpoint_hash_initial_run', 'outpoint_hash_initial_execution']}
    if len(results) != 2 or set(results) != set(expected) or definitions != [ROOT + '.op_initial_run'] or deps != expected:
        raise ValueError('expected exactly two six-dependency results and one definition')


def identity(external):
    parent = json.loads((PARENT / 'RUN.json').read_text())
    startup = json.loads((START / 'CHECKED.json').read_text())
    work, parent_ext, init_ext = Path(parent['candidate']), Path(parent['external']), Path(startup['external'])
    _, parent_sources, inherited, extra = local.identity(parent_ext)
    if not startup['recursive_kernel_check'] or startup['kernel']['exit_code'] != 0 or Path(startup['candidate']) != work:
        raise ValueError('checked startup/frame-construction basis required')
    if parent['main_inputs'] != s.input_map() or parent['staged_patch_sha256'] != s.index_hash():
        raise ValueError('lifecycle compile input identity differs')
    if parent['tools_sha256'] != {'verify.py': s.sha((PARENT / 'verify.py').read_bytes()),
        'SOURCE-REVIEW.json': s.sha((PARENT / 'SOURCE-REVIEW.json').read_bytes())}:
        raise ValueError('lifecycle driver differs')
    for m, p in parent_sources + [('EntropyReady.Init', init_ext / 'Init.v')]:
        archived = (PARENT if m.startswith('OutpointLocal.') else START) / (p.name + '.source')
        r = parent if m.startswith('OutpointLocal.') else startup
        row = dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
        if p.is_symlink() or p.read_bytes() != archived.read_bytes() or row != r['extension_sources_objects'][m]:
            raise ValueError('inherited source/object differs: ' + m)
        inherited[m] = row
    if (external in [work, parent_ext, init_ext, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {'Ready.v'}):
        raise ValueError('distinct exact external ready tree required')
    source = external / 'Ready.v'
    if source.is_symlink() or source.read_bytes() != (HERE / 'Ready.v.source').read_bytes():
        raise ValueError('ready archive differs')
    s.safe_source(source.read_text(), ROOT)
    return work, source, inherited, startup, extra + ['-Q', str(init_ext), 'EntropyReady', '-Q', str(external), 'OutpointReady']


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('ready compile already recorded')
    work, source, inherited, startup, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {'outpoint-ready-fresh': s.run(work,
        ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], 'outpoint-ready-fresh', 60)}
    results, definitions, deps = g.reports(work, [(ROOT, source)], 'outpoint-ready', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('ready library query failed')
    imports = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    bound = startup['loaded_local_source_objects']
    if len(imports) != 261 or not imports <= set(bound):
        raise ValueError('ready imports lack exact source-bound provenance')
    extensions = set(re.findall(r'^  ((?:OutpointReady|OutpointLocal|OutpointMiddle|OutpointExec|AssetLocal|NonceLocal|NonceExec|NonceContext|EntropyReady)\.[A-Za-z0-9_.]+)$',
                               query.stdout, re.M))
    if extensions != {ROOT} | set(inherited):
        raise ValueError('ready extension inventory differs')
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('ready compilation changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_local_compile_sha256=s.sha((PARENT / 'RUN.json').read_bytes()),
        startup_checked_sha256=s.sha((START / 'CHECKED.json').read_bytes()),
        loaded_local_source_objects={n: bound[n] for n in sorted(imports)},
        inherited_extension_sources_objects=inherited,
        extension_sources_objects={ROOT: dict(source_sha256=s.sha(source.read_bytes()),
                                             object_sha256=s.sha(source.with_suffix('.vo').read_bytes()))},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', memcpy_model_explicit=True, all_logical_inputs=True,
        actual_program_initial_memory=True, input_and_output_frames_constructed=True,
        frame_and_startup_premises_discharged=True, invalid_contexts_not_excluded=True,
        public_frame_jet_lifecycle_proved=True, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Every outpoint input executes from actual initialization; two exact SIX results and 261 source-bound imports', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('ready kernel already launched; inspect original process')
    work, source, inherited, startup, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('outpoint_ready_bound_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, current, _, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or r['inherited_extension_sources_objects'] != current or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_local_compile_sha256'] != s.sha((PARENT / 'RUN.json').read_bytes()) or
            r['startup_checked_sha256'] != s.sha((START / 'CHECKED.json').read_bytes()) or
            r['extension_sources_objects'] != {ROOT: dict(source_sha256=s.sha(source.read_bytes()),
                object_sha256=s.sha(source.with_suffix('.vo').read_bytes()))}):
            raise ValueError('ready checked-input identity differs')
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'outpoint-ready-kernel', 3600)
    log = (work / 'outpoint-ready-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'outpoint-ready-kernel.log': log})
    print('Every original outpoint_hash input executes from real initialization: recursive kernel check passed', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
