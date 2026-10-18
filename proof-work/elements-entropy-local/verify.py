"""Audit the complete original entropy frame jet without normal registration."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
STREAM = HERE.parent / 'elements-entropy-stream'
PREFIX = HERE.parent / 'elements-entropy-frame-read'
sp = importlib.util.spec_from_file_location('entropy_local_stream', STREAM / 'verify.py')
stream = importlib.util.module_from_spec(sp)
sp.loader.exec_module(stream)
s, g = stream.s, stream.g
NAMES = ['Common', 'Inputs', 'Shape', 'Writer', 'Local']
MODULES = ['EntropyCompose.' + n for n in NAMES]
ROOT = 'EntropyCompose.Local'


def profile(results, definitions, deps):
    four = ['Common.calc_local_addr', 'Common.calc_local_array', 'Inputs.entropy_local_txid', 'Writer.calc_mid_arg']
    six = ['Common.exec_calc_result_copy', 'Common.exec_source_copy', 'Common.exec_calc_write',
           'Inputs.exec_entropy_read_array', 'Inputs.exec_entropy_read_index', 'Inputs.exec_entropy_store_index',
           'Shape.exec_entropy_helper', 'Shape.entropy_function_composes', 'Writer.calc_writehash_wrap',
           'Writer.calc_writehash_from_frame', 'Local.calculate_issuance_entropy_local_spec']
    expected = {n: set() for n in results}
    expected.update({'EntropyCompose.' + n: stream.base.FOUR for n in four})
    expected.update({'EntropyCompose.' + n: s.SIX for n in six})
    if (len(results), len(definitions)) != (27, 18) or deps != expected:
        raise ValueError('complete profile differs: expected 12 closed, four four-dependency, eleven six-dependency results')


def identity(external):
    parent = json.loads((STREAM / 'CHECKED.json').read_text())
    prefix = json.loads((PREFIX / 'RUN.json').read_text())
    work, bridge, read = Path(parent['candidate']), Path(parent['external']), Path(prefix['external'])
    if not parent['recursive_kernel_check'] or parent['kernel']['exit_code'] != 0:
        raise ValueError('completed source-bound helper kernel check required')
    stream.identity(bridge)
    if Path(prefix['candidate']) != work:
        raise ValueError('prefix and helper target trees differ')
    force = s.load('entropy_local_bound_objects', HERE.parent / 'verify-forced-closure.py')
    force.objects(work, parent['loaded_local_source_objects'])
    inherited = {}
    for record, root, archive in [(parent, bridge, STREAM), (prefix, read, PREFIX)]:
        for module, row in record['extension_sources_objects'].items():
            if archive == STREAM and module == 'EntropyRegisters.Registers':
                source = bridge / 'regs/Registers.v'
                archived = HERE.parent / 'elements-entropy-registers/Registers.v.source'
            else:
                source = root / (module.rsplit('.', 1)[1] + '.v')
                archived = archive / (source.name + '.source')
            if (source.is_symlink() or source.read_bytes() != archived.read_bytes() or
                row != dict(source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()))):
                raise ValueError('inherited extension source/object changed: ' + module)
            inherited[module] = row
    sources = [(m, external / (n + '.v')) for m, n in zip(MODULES, NAMES)]
    if (external in [work, bridge, read, s.REPO] or s.REPO in external.parents or
        {p.name for p in external.glob('*.v')} != {n + '.v' for n in NAMES}):
        raise ValueError('distinct exact external composition tree required')
    for module, source in sources:
        if source.is_symlink() or source.read_bytes() != (HERE / (source.name + '.source')).read_bytes():
            raise ValueError('composition archive differs: ' + module)
        s.safe_source(source.read_text(), module)
    extra = ['-Q', str(read), 'EntropyFrame', '-Q', str(external), 'EntropyCompose',
             '-Q', str(bridge), 'EntropyStreaming', '-Q', str(bridge / 'regs'), 'EntropyRegisters']
    return work, sources, parent, inherited, extra


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('composition compilation already recorded')
    work, sources, parent, inherited, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for module, source in sources:
        stem = 'entropy-local-' + source.stem.lower() + '-fresh'
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], stem, 60)
    results, definitions, deps = g.reports(work, sources, 'entropy-local', commands, extra)
    profile(results, definitions, deps)
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ROOT + '.\nPrint Libraries.\n', cwd=work / 'Coq',
        env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('composition library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    if len(local) != 278 or local != set(parent['loaded_local_source_objects']):
        raise ValueError('composition project imports differ from source-bound helper closure')
    extensions = set(re.findall(r'^  ((?:EntropyCompose|EntropyFrame|EntropyStreaming|EntropyRegisters)\.[A-Za-z0-9_.]+)$',
                               query.stdout, re.M))
    if extensions != set(MODULES) | set(inherited):
        raise ValueError('composition extension inventory differs')
    own = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
           for m, p in sources}
    identity(external)
    if before != s.input_map() or index != s.index_hash():
        raise ValueError('composition compilation changed main/index')
    record = dict(candidate=str(work), external=str(external), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        parent_stream_compile_sha256=s.sha((STREAM / 'RUN.json').read_bytes()),
        parent_stream_checked_sha256=s.sha((STREAM / 'CHECKED.json').read_bytes()),
        parent_prefix_compile_sha256=s.sha((PREFIX / 'RUN.json').read_bytes()),
        loaded_local_source_objects=parent['loaded_local_source_objects'], inherited_extension_sources_objects=inherited,
        extension_sources_objects=own, tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', logical_input_bits=544, output_bits=256,
        public_frame_jet_lifecycle_proved=True, canonical_word_program=True,
        memcpy_model_explicit=True, dispatch_and_max_counter_explicit=True,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Original entropy frame-jet equivalence compiled; 27-result exact profile and 278 source-bound imports verified', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('composition kernel already launched; inspect original process')
    work, sources, parent, inherited, extra = identity(external)
    r = json.loads((HERE / 'RUN.json').read_text())

    def bound():
        _, _, current, current_inherited, _ = identity(external)
        profile(r['results'], r['definitions'], {n: set(d) for n, d in r['dependencies'].items()})
        if (r['external'] != str(external) or r['main_inputs'] != s.input_map() or
            r['staged_patch_sha256'] != s.index_hash() or
            r['loaded_local_source_objects'] != current['loaded_local_source_objects'] or
            r['inherited_extension_sources_objects'] != current_inherited or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_stream_compile_sha256'] != s.sha((STREAM / 'RUN.json').read_bytes()) or
            r['parent_stream_checked_sha256'] != s.sha((STREAM / 'CHECKED.json').read_bytes()) or
            r['parent_prefix_compile_sha256'] != s.sha((PREFIX / 'RUN.json').read_bytes())):
            raise ValueError('composition checked-input identity differs')
        for m, p in sources:
            if r['extension_sources_objects'][m] != dict(source_sha256=s.sha(p.read_bytes()),
                object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
                raise ValueError('composition source/object changed: ' + m)
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [ROOT])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'entropy-local-kernel', 3600)
    log = (work / 'entropy-local-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'entropy-local-kernel.log': log})
    print('Complete original entropy frame-jet equivalence recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
