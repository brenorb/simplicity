"""Source-bound compile/report/kernel audit of three original calculation jets."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('local_recovery', HERE / 'recovery.py')
r = importlib.util.module_from_spec(sp)
sp.loader.exec_module(r)
s, g, c, b = r.s, r.g, r.c, r.b
LIFE = HERE.parent / 'elements-calculation-lifecycle'
sp = importlib.util.spec_from_file_location('lifecycle_profile', LIFE / 'verify.py')
life = importlib.util.module_from_spec(sp)
sp.loader.exec_module(life)
MODULE = 'CalculationLocal.Local'


def main(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('local audit already recorded; inspect original process')
    bound = json.loads((r.OUT / 'SOURCE-CLOSURE.json').read_text())
    basis = json.loads((r.OUT / 'RUN.json').read_text())
    if Path(bound['candidate']) != work:
        raise ValueError('recovery candidate differs')
    force = s.load('local_recovery_closure', HERE.parent / 'verify-forced-closure.py')
    names = ['Entry', 'Allocation', 'Shape', 'Read', 'Writer']
    srcs = [('CalculationLifecycle.' + n, work / 'extension/lifecycle' / (n + '.v'), LIFE / (n + '.v.source'))
            for n in names]
    srcs += [('CalculationCalls.CalculationCalls', work / 'extension/calls/CalculationCalls.v',
              r.BASE / 'CalculationCalls.v.source'),
             (MODULE, work / 'extension/local/Local.v', HERE / 'Local.v.source')]
    extra = ['-Q', str(work / 'extension/lifecycle'), 'CalculationLifecycle',
             '-Q', str(work / 'extension/calls'), 'CalculationCalls',
             '-Q', str(work / 'extension/local'), 'CalculationLocal']
    s.changed({p: archive.read_text() for _, p, archive in srcs})

    def identity():
        b.tree(work)
        force.objects(work, bound['compiled_and_loaded_local_modules'])
        if (s.sha((r.OUT / 'RUN.json').read_bytes()) != bound['compile_sha256'] or
            basis['tools_sha256'] != {'recovery.py': s.sha((HERE / 'recovery.py').read_bytes()),
                'basis.py': s.sha((r.BASE / 'basis.py').read_bytes()),
                'calls.py': s.sha((r.BASE / 'calls.py').read_bytes())}):
            raise ValueError('recovery basis identity changed')
        c.basis_profile(basis)
        for module, p, archive in srcs:
            if p.is_symlink() or p.read_bytes() != archive.read_bytes():
                raise ValueError('extension source/archive differs: ' + module)
            s.safe_source(p.read_text(), module)
        if {p for p in (work / 'extension').rglob('*.v')} != {p for _, p, _ in srcs}:
            raise ValueError('unexpected external source inventory')

    identity()
    before, index = s.input_map(), s.index_hash()
    commands = {}
    for module, p, _ in srcs:
        stem = 'local-fresh-' + module.replace('.', '-')
        commands[stem] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', *extra, str(p)], stem, 60)
    results, definitions, deps = g.reports(work, [(m, p) for m, p, _ in srcs], 'local', commands, extra)
    old_life = json.loads((LIFE / 'RUN.json').read_text())
    old_calls = json.loads((r.BASE / 'CALLS-RUN.json').read_text())
    life.profile(old_life['results'], old_life['definitions'],
                 {n: set(d) for n, d in old_life['dependencies'].items()})
    expected = {n: set(d) for row in [old_life, old_calls] for n, d in row['dependencies'].items()}
    expected.update({MODULE + '.' + n: s.SIX for n in ['calculation_jet_from_helper',
        'calculate_asset_local_spec', 'calculate_explicit_token_local_spec', 'calculate_confidential_token_local_spec']})
    expected.update({MODULE + '.' + n: set() for n in ['calc_asset_not_local',
        'calc_token_not_local', 'calc_asset_link', 'calc_token_link']})
    if (len(results), len(definitions)) != (47, 23) or deps != expected:
        raise ValueError('full 47-result/23-definition exact assumption inventory differs')
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet', *extra]
    query = subprocess.run(command, input='Require ' + ' '.join(m for m, _, _ in srcs) + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=60)
    if query.returncode or re.search(r'(?m)^(?:Error|Anomaly):', query.stdout):
        raise ValueError('cannot inspect full local-jet dependency closure')
    local = {m.replace('.', '/') + '.v' for m in
        re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', query.stdout, re.M)}
    if local != set(bound['compiled_and_loaded_local_modules']):
        raise ValueError('local-jet dependency closure differs from fresh forced-source basis')
    extension = set(re.findall(r'^  (Calculation(?:Lifecycle|Calls|Local)\.[A-Za-z0-9_.]+)$', query.stdout, re.M))
    if extension != {m for m, _, _ in srcs}:
        raise ValueError('unexpected extension dependency inventory')
    objects = {m: dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes()))
               for m, p, _ in srcs}
    identity()
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('local compile changed main inputs or staging')
    record = dict(candidate=str(work), main_inputs=before, staged_patch_sha256=index,
        commands=commands, results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        basis_source_closure_sha256=s.sha((r.OUT / 'SOURCE-CLOSURE.json').read_bytes()),
        loaded_local_source_objects=bound['compiled_and_loaded_local_modules'], extension_sources_objects=objects,
        tools_sha256={'check.py': s.sha(Path(__file__).read_bytes())},
        library_query=dict(command=command, exit_code=query.returncode, log_sha256=s.sha(query.stdout.encode())),
        actual_target_genv='elements_ge', recursive_kernel_check=False,
        public_frame_jet_lifecycle_proved=True, concrete_frame_jet_theorems=3,
        memcpy_model_explicit=True, initial_dispatch_premise_explicit=True,
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        HERE / 'loaded-libraries.log': query.stdout,
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Three original frame-jet equivalence contracts compiled with full reports; starting recursive kernel audit', flush=True)
    command = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o '
               + ' '.join(extra + [MODULE])]
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(dict(command=command,
        compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()), recursive_kernel_check=False), indent=2) + '\n'})
    row = s.run(work, command, 'local-kernel', 3600)
    log = (work / 'local-kernel.log').read_text()
    expected_context = sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split())
    s.kernel.kernel(log, expected_context)
    identity()
    for m, p, _ in srcs:
        if objects[m] != dict(source_sha256=s.sha(p.read_bytes()), object_sha256=s.sha(p.with_suffix('.vo').read_bytes())):
            raise ValueError('extension source/object changed during kernel check')
    if record['tools_sha256'] != {'check.py': s.sha(Path(__file__).read_bytes())}:
        raise ValueError('local audit driver changed during kernel check')
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('local kernel check changed main inputs or staging')
    record.update(recursive_kernel_check=True, kernel=row, exact_library_context=expected_context,
        kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n', HERE / 'local-kernel.log': log})
    print('Three original calculation frame jets recursively kernel-checked; libc/dispatch remain explicit', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise ValueError('usage: check.py PRIVATE_RECOVERY_TREE')
    main(Path(sys.argv[1]).resolve())
