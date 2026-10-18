"""Check initialization and frame construction for the original entropy jet."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'elements-entropy-local'
sp = importlib.util.spec_from_file_location('entropy_ready_local', BASE / 'verify.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.g
NAMES = ['Init', 'Ready']
ROOT = 'EntropyReady.Ready'
FRAME = 'C/jet_frame_constructible.v'


def identity(external):
    parent = json.loads((BASE / 'RUN.json').read_text())
    work, compose = Path(parent['candidate']), Path(parent['external'])
    _, _, _, inherited, extra = base.identity(compose)
    force = s.load('entropy_ready_bound_objects', HERE.parent / 'verify-forced-closure.py')
    force.objects(work, parent['loaded_local_source_objects'])
    inherited = dict(inherited)
    for m, row in parent['extension_sources_objects'].items():
        p = compose / (m.rsplit('.', 1)[1] + '.v')
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('parent composition source/object changed: ' + m)
        inherited[m] = row
    sources = [('EntropyReady.' + n, external / (n + '.v')) for n in NAMES]
    if (external in [work, compose, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external readiness tree required')
    for m, source in sources:
        if source.is_symlink() or source.read_bytes() != (HERE / (source.name + '.source')).read_bytes():
            raise ValueError('readiness source/archive differs: ' + m)
        s.safe_source(source.read_text(), m)
    if (work / 'Coq' / FRAME).read_bytes() != (s.REPO / 'Coq' / FRAME).read_bytes():
        raise ValueError('constructibility helper differs from original main source')
    return work, sources, parent, inherited, extra + ['-Q', str(external), 'EntropyReady']


def profile(results, definitions, deps):
    expected = {n: set() for n in results}
    for n in ['entropy_pointer_initialized', 'entropy_startup_initialized']:
        expected['EntropyReady.Init.' + n] = base.stream.base.FOUR
    for n in ['calculate_issuance_entropy_initial_run', 'calculate_issuance_entropy_initial_execution']:
        expected['EntropyReady.Ready.' + n] = s.SIX
    if (len(results), len(definitions)) != (13, 4) or deps != expected:
        raise ValueError('expected nine closed, two four-dependency, two six-dependency results and four definitions')


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('readiness compilation already recorded')
    work, sources, parent, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {'entropy-ready-frame-fresh': s.run(work,
        ['bash', 'build-jets.sh', '--coqc', '-q', FRAME], 'entropy-ready-frame-fresh', 120)}
    for m, source in sources:
        stem = 'entropy-ready-' + source.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'entropy-ready', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('readiness library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    objects = dict(parent['loaded_local_source_objects'])
    if local != set(objects) | {FRAME}:
        raise ValueError('unreviewed readiness project dependency')
    source = work / 'Coq' / FRAME
    objects[FRAME] = dict(source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()))
    extensions = set(re.findall(r'^  ((?:EntropyCompose|EntropyFrame|EntropyStreaming|EntropyRegisters|EntropyReady)\.[A-Za-z0-9_.]+)$',
                               query.stdout, re.M))
    if extensions != set(inherited) | {m for m, _ in sources}:
        raise ValueError('unreviewed readiness extension dependency')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('readiness compilation changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_compile_sha256=s.sha((BASE / 'RUN.json').read_bytes()), loaded_local_source_objects=objects,
        inherited_extension_sources_objects=inherited, extension_sources_objects=own,
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        memcpy_model_explicit=True, startup_premises_discharged=True,
        frame_premises_constructed_for_every_input=True, init_mem_existence_proved=True,
        public_frame_jet_lifecycle_proved=True, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Entropy jet initial-memory execution compiled for every input; thirteen-result profile and 279-source closure verified', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('readiness kernel already launched; inspect original process')
    work, sources, parent, inherited, extra = identity(external)
    checked = json.loads((BASE / 'CHECKED.json').read_text())
    if not checked['recursive_kernel_check'] or checked['kernel']['exit_code'] != 0:
        raise ValueError('completed full-jet parent kernel check required')
    r = json.loads((HERE / 'RUN.json').read_text())
    parent_checked_sha = s.sha((BASE / 'CHECKED.json').read_bytes())
    force = s.load('entropy_ready_kernel_objects', HERE.parent / 'verify-forced-closure.py')

    def bound():
        _, _, _, current_inherited, _ = identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or
            r['inherited_extension_sources_objects'] != current_inherited or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_compile_sha256'] != s.sha((BASE / 'RUN.json').read_bytes()) or
            parent_checked_sha != s.sha((BASE / 'CHECKED.json').read_bytes())):
            raise ValueError('readiness checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('readiness source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), parent_checked_sha256=parent_checked_sha,
        recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'entropy-ready-kernel', 3600)
    log = (work / 'entropy-ready-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'entropy-ready-kernel.log': log})
    print('Entropy jet execution from actual initialization recursively kernel-checked for every logical input', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
