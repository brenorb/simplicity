"""Fresh source/object-bound initialization and constructibility extension."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'elements-calculation-local'
sp = importlib.util.spec_from_file_location('ready_base', BASE / 'check.py')
base = importlib.util.module_from_spec(sp)
sp.loader.exec_module(base)
s, g = base.s, base.g
MODULE = 'CalculationReady.Ready'
FRAME = 'C/jet_frame_constructible.v'


def identity(external):
    r = json.loads((BASE / 'RUN.json').read_text())
    work = Path(r['candidate'])
    base.b.tree(work)
    force = s.load('ready_bound_objects', HERE.parent / 'verify-forced-closure.py')
    force.objects(work, r['loaded_local_source_objects'])
    if r['tools_sha256'] != {'check.py': s.sha((BASE / 'check.py').read_bytes())}:
        raise ValueError('enclosing jet driver changed')
    for m, row in r['extension_sources_objects'].items():
        ns, n = m.split('.')
        directory = {'CalculationLifecycle': 'lifecycle', 'CalculationCalls': 'calls', 'CalculationLocal': 'local'}[ns]
        p = work / 'extension' / directory / (n + '.v')
        if row != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('enclosing jet source/object changed: ' + m)
    p = external / 'Ready.v'
    if (external == work or external == s.REPO or s.REPO in external.parents or
        p.is_symlink() or p.read_bytes() != (HERE / 'Ready.v.source').read_bytes() or
        {f.name for f in external.glob('*.v')} != {'Ready.v'}):
        raise ValueError('distinct exact readiness source required')
    s.safe_source(p.read_text(), MODULE)
    extra = ['-Q', str(work / 'extension/lifecycle'), 'CalculationLifecycle',
             '-Q', str(work / 'extension/calls'), 'CalculationCalls',
             '-Q', str(work / 'extension/local'), 'CalculationLocal',
             '-Q', str(external), 'CalculationReady']
    return r, work, p, extra


def compile(external):
    if (HERE / 'RUN.json').exists():
        raise ValueError('readiness compile already recorded')
    parent, work, source, extra = identity(external)
    before, index = s.input_map(), s.index_hash()
    commands = {}
    commands['ready-frame-fresh'] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', FRAME], 'ready-frame-fresh', 120)
    commands['ready-fresh'] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(source)], 'ready-fresh', 60)
    results, definitions, deps = g.reports(work, [(MODULE, source)], 'ready', commands, extra)
    expected = {n: set() for n in results}
    expected.update({MODULE + '.' + n: base.c.FOUR for n in ['calc_pointer_initialized', 'calc_dispatch_initialized']})
    expected.update({MODULE + '.' + n: s.SIX for n in ['calculation_local_initial_run',
        'calculate_asset_initial_run', 'calculate_explicit_token_initial_run', 'calculate_confidential_token_initial_run']})
    if (len(results), len(definitions)) != (14, 4) or deps != expected:
        raise ValueError('exact 14-result/4-definition readiness dependency profile differs')
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + MODULE + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('readiness loaded-library query failed')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    if local != set(parent['loaded_local_source_objects']) | {FRAME}:
        raise ValueError('unreviewed readiness source dependency')
    extensions = set(re.findall(r'^  (Calculation(?:Lifecycle|Calls|Local|Ready)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extensions != set(parent['extension_sources_objects']) | {MODULE}:
        raise ValueError('unexpected readiness extension dependency')
    objects = dict(parent['loaded_local_source_objects'])
    objects[FRAME] = dict(source_sha256=s.sha((work / 'Coq' / FRAME).read_bytes()),
                          object_sha256=s.sha((work / 'Coq' / FRAME).with_suffix('.vo').read_bytes()))
    if objects[FRAME]['source_sha256'] != s.sha((s.REPO / 'Coq' / FRAME).read_bytes()):
        raise ValueError('constructibility helper differs from main source')
    identity(external)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('readiness compile changed main inputs or staging')
    record = dict(candidate=str(work), external=str(external), main_inputs=before,
        staged_patch_sha256=index, commands=commands, results=results, definitions=definitions,
        dependencies={n: sorted(d) for n, d in deps.items()}, loaded_local_source_objects=objects,
        parent_compile_sha256=s.sha((BASE / 'RUN.json').read_bytes()),
        source_sha256=s.sha(source.read_bytes()), object_sha256=s.sha(source.with_suffix('.vo').read_bytes()),
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        memcpy_model_explicit=True, initial_dispatch_premise_discharged=True,
        frame_premises_constructed_for_every_input=True, init_mem_existence_proved=True,
        recursive_kernel_check=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n', HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Initial-memory corollaries, real dispatch initializer and initial-memory existence fully compiled/reported', flush=True)


def kernel(external):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('readiness kernel already launched; inspect its original process')
    parent, work, source, extra = identity(external)
    if not json.loads((BASE / 'CHECKED.json').read_text())['recursive_kernel_check']:
        raise ValueError('wait for the enclosing local-jet kernel run to finish first')
    r = json.loads((HERE / 'RUN.json').read_text())
    force = s.load('ready_kernel_source_objects', HERE.parent / 'verify-forced-closure.py')
    def bound():
        identity(external)
        force.objects(work, r['loaded_local_source_objects'])
        if (r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['source_sha256'] != s.sha(source.read_bytes()) or
            r['object_sha256'] != s.sha(source.with_suffix('.vo').read_bytes()) or
            r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())} or
            r['parent_compile_sha256'] != s.sha((BASE / 'RUN.json').read_bytes())):
            raise ValueError('readiness bound input identity changed')
    bound()
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [MODULE])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'ready-kernel', 3600)
    log = (work / 'ready-kernel.log').read_text()
    s.kernel.kernel(log, sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    bound()
    r.update(recursive_kernel_check=True, kernel=row,
             kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n', HERE / 'ready-kernel.log': log})
    print('Three original calculation initial-memory corollaries recursively kernel-checked; memcpy_model remains explicit', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel EXTERNAL_DIRECTORY')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
