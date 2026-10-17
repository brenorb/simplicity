"""Forced source-bound verification of the three original issuance getters."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('computed_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('computed_reports', HERE.parent / 'elements-tap-getters/check.py')
CALC = 'C.jet_elements_issuance_calc_spec'
SPEC = 'C.jet_elements_issuance_entropy_spec'
EXEC = 'C.jet_elements_issuance_computed_exec'
MODULE = 'C.jet_elements_issuance_computed_local'
MODULES = [CALC, SPEC, EXEC, MODULE]
ARCHIVES = [('elements-issuance-status', n) for n in [
    'jet_elements_indexed_tag3_exec', 'jet_elements_indexed_tag3_gen',
    'jet_elements_issuance_status_spec', 'jet_elements_issuance_status_exec']]
ARCHIVES += [('elements-issuance-computed', n.removeprefix('C.')) for n in MODULES]
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + MODULE]


def inherited(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('distinct private tree required')
    subprocess.run(['git', 'diff', '--quiet', '91d89bac', '--', 'C', 'Haskell',
                    'Coq/Simplicity', ':(exclude)C/test.c'], cwd=s.REPO, check=True)
    for name, digest in s.input_map().items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('current inherited source/input differs: ' + name)


def tree(work):
    inherited(work)
    expected = {name[4:] for name in s.input_map() if name.startswith('Coq/')}
    for folder, stem in ARCHIVES:
        path = work / 'Coq/C' / (stem + '.v')
        if path.is_symlink() or path.read_bytes() != (HERE.parent / folder / 'source' / (stem + '.v.source')).read_bytes():
            raise ValueError('private/archive proof differs: ' + stem)
        s.safe_source(path.read_text(), stem)
        expected.add('C/' + stem + '.v')
    if g.inventory(work / 'Coq') != expected:
        raise ValueError('unexpected source inventory')


def prepare(work):
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('already prepared; inspect the original candidate')
    inherited(work)
    before, index = s.input_map(), s.index_hash()
    changes = {}
    for folder, stem in ARCHIVES:
        target = work / 'Coq/C' / (stem + '.v')
        if target.exists():
            raise ValueError('refuse to overwrite existing candidate source: ' + stem)
        changes[target] = (HERE.parent / folder / 'source' / (stem + '.v.source')).read_text()
    s.changed(changes)
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('preparation changed main/index')
    s.changed({HERE / 'PREPARATION.json': json.dumps(dict(candidate=str(work),
        staged_patch_sha256=index, coverage_added=0), indent=2) + '\n'})
    print('Prepared eight additive sources in the distinct private tree', flush=True)


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('compile receipt already exists')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    runtime = Path(s.ENV['COMPCERT']).parent
    flags = []
    for name in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(Path(s.ENV['COMPCERT']) / name), 'compcert.' + name]
    flags += ['-R', str(Path(s.ENV['COMPCERT']) / 'flocq'), 'Flocq']
    for name in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(runtime / 'vst-2.14' / name), 'VST.' + name]
    flags += ['-Q', str(runtime / 'vst-2.14/sha'), 'sha']
    g.LM = MODULE
    extras = [n.replace('.', '/') + '.v' for n in g.closure(work / 'Coq')]
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-f', '_CoqProject.jets', *extras,
        *flags, '-o', 'ComputedIssuanceProofMakefile'], 'makefile', 60)
    commands['build'] = s.run(work, ['make', '-f', 'ComputedIssuanceProofMakefile', '-B', '-j2',
        MODULE.replace('.', '/') + '.vo'], 'build', 5400)
    for module in MODULES:
        commands['fresh-' + module] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q',
            module.replace('.', '/') + '.v'], 'fresh-' + module, 60)
    results, definitions, deps = g.reports(work,
        [(m, work / 'Coq' / (m.replace('.', '/') + '.v')) for m in MODULES], 'computed', commands)
    endpoints = [MODULE + '.elements_issuance_' + n + '_local_spec' for n in ['entropy', 'asset', 'token']]
    funext = [SPEC + '.elements_issuance_' + n + '_sem' for n in ['entropy', 'asset', 'token']]
    execution = [EXEC + '.exec_computed_issuance_setup', EXEC + '.exec_computed_issuance_payload',
                 MODULE + '.computed_issuance_hash_local', *endpoints]
    pure_compcert = [EXEC + '.eval_computed_issuance_hash_addr']
    closed = [n for n in results if n not in endpoints + funext + execution + pure_compcert]
    expected = {n: set() for n in closed}
    expected.update({n: {'FunctionalExtensionality.functional_extensionality_dep'} for n in funext})
    expected.update({n: s.SIX for n in execution})
    expected.update({n: s.SIX - {'Events.external_functions_sem', 'Events.inline_assembly_sem'} for n in pure_compcert})
    if (len(results), len(definitions), len(closed), len(endpoints)) != (25, 29, 15, 3) or deps != expected:
        raise ValueError('unexpected full result/type/assumption inventory')
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('verification changed main/index')
    record = dict(candidate=str(work), starting_revision='91d89bac',
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work), main_inputs=before,
        staged_patch_sha256=index, commands=commands, results=results, definitions=definitions,
        endpoints=endpoints, dependencies={n: sorted(d) for n, d in deps.items()},
        sources_sha256={n: s.sha((work / 'Coq/C' / (n + '.v')).read_bytes()) for _, n in ARCHIVES},
        objects_sha256={n: s.sha((work / 'Coq/C' / (n + '.vo')).read_bytes()) for _, n in ARCHIVES},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        force_rebuilt_entire_local_closure=True, historical_acceptance_reused=False,
        caller_cached_hashes_established=False, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
               **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Three original issuance getter candidates freshly compiled; complete types and assumptions checked', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; inspect the original process')
    r = json.loads((HERE / 'RUN.json').read_text())
    tree(work)
    if (r['candidate'] != str(work) or r['main_inputs'] != s.input_map() or
        r['staged_patch_sha256'] != s.index_hash() or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())}):
        raise ValueError('compile identity differs')
    for field, suffix in [('sources_sha256', '.v'), ('objects_sha256', '.vo')]:
        for n, digest in r[field].items():
            if s.sha((work / 'Coq/C' / (n + suffix)).read_bytes()) != digest:
                raise ValueError('checked source/object changed: ' + n)
    launch = dict(candidate=str(work), command=KERNEL, compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
                  recursive_kernel_check=False)
    s.changed({HERE / 'KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    commands = dict(r['commands'])
    commands['kernel'] = s.run(work, KERNEL, 'kernel', 3600)
    s.kernel.kernel((work / 'kernel.log').read_text(),
                    sorted((work / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    tree(work)
    if (r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('kernel changed source/main/index')
    r.update(commands=commands, recursive_kernel_check=True,
             kernel_launch_sha256=s.sha((HERE / 'KERNEL-RUN.json').read_bytes()))
    s.changed({HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n',
               HERE / 'kernel.log': (work / 'kernel.log').read_text()})
    print('Three original issuance getters recursively kernel-checked; normal admission remains separate', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['prepare', 'compile', 'kernel']:
        raise ValueError('usage: verify.py prepare|compile|kernel PRIVATE_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
