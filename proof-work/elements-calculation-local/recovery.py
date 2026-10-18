"""Fresh recovery after the original temporary proof trees disappeared.

Never overwrite earlier receipts or accept objects solely by their old hashes.
"""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'elements-calculation-calls'
sp = importlib.util.spec_from_file_location('calculation_recovery_base', BASE / 'calls.py')
c = importlib.util.module_from_spec(sp)
sp.loader.exec_module(c)
b, s, g = c.base, c.s, c.g
OUT = HERE / 'recovery-basis'


def build(work):
    if (OUT / 'RUN.json').exists():
        raise ValueError('fresh recovery already recorded; inspect its original process')
    b.tree(work)
    before, index = s.input_map(), s.index_hash()
    flags = []
    for n in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(Path(s.ENV['COMPCERT']) / n), 'compcert.' + n]
    flags += ['-R', str(Path(s.ENV['COMPCERT']) / 'flocq'), 'Flocq']
    runtime = Path(s.ENV['COMPCERT']).parent
    for n in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(runtime / 'vst-2.14' / n), 'VST.' + n]
    flags += ['-Q', str(runtime / 'vst-2.14/sha'), 'sha']
    extras = set()
    for root in b.ROOTS:
        g.LM = root
        extras.update(n.replace('.', '/') + '.v' for n in g.closure(work / 'Coq'))
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-f', '_CoqProject.jets',
        *sorted(extras), *flags, '-o', 'RecoveryMakefile'], 'recovery-makefile', 60)
    print('Fresh recovery: forcing the original calculation helper source closure', flush=True)
    commands['build'] = s.run(work, ['make', '-f', 'RecoveryMakefile', '-B', '-j2',
        *(n.replace('.', '/') + '.vo' for n in b.ROOTS)], 'recovery-build', 5400)
    modules = [('C.' + n, work / 'Coq/C' / (n + '.v')) for n in b.NAMES]
    results, definitions, deps = g.reports(work, modules, 'recovery-basis', commands)
    c.basis_profile(dict(results=results, definitions=definitions, dependencies=deps))
    b.tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('recovery build changed main inputs or staging')
    record = dict(candidate=str(work), starting_revision='91d89bac', main_inputs=before,
        staged_patch_sha256=index, commands=commands, roots=b.ROOTS,
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        proof_loading_aliases={b.ALIAS: b.TARGET},
        force_rebuilt_entire_local_closure=True, recursive_kernel_check=False,
        tools_sha256={'recovery.py': s.sha(Path(__file__).read_bytes()),
                      'basis.py': s.sha((BASE / 'basis.py').read_bytes()),
                      'calls.py': s.sha((BASE / 'calls.py').read_bytes())},
        normal_registration=False, coverage_added=0)
    s.changed({OUT / 'RUN.json': json.dumps(record, indent=2) + '\n',
        OUT / 'build.log': (work / 'recovery-build.log').read_text(),
        **{OUT / (stem + '.log'): (work / (stem + '.log')).read_text()
           for stem in ['recovery-makefile', 'recovery-basis-assumptions', 'recovery-basis-contracts']}})
    force = s.load('recovery_source_closure', HERE.parent / 'verify-forced-closure.py')
    force.snapshot(OUT, b.ROOTS)
    bound = json.loads((OUT / 'SOURCE-CLOSURE.json').read_text())
    old = json.loads((BASE / 'SOURCE-CLOSURE.json').read_text())
    if ({n: r['source_sha256'] for n, r in bound['compiled_and_loaded_local_modules'].items()} !=
        {n: r['source_sha256'] for n, r in old['compiled_and_loaded_local_modules'].items()}):
        raise ValueError('recovery source closure differs from the reviewed original-program basis')
    print('Recovered the same 196 source modules with fresh objects and exact per-result dependencies', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'build':
        raise ValueError('usage: recovery.py build PRIVATE_TREE')
    build(Path(sys.argv[2]).resolve())
