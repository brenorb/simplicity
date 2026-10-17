"""Current-source verification only; historical /tmp receipts are not reused."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('composite_amounts_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('composite_amounts_reports', HERE.parent / 'elements-tap-getters/check.py')
MODULE = 'C.jet_elements_composite_amounts_hash'
NEW = 'C/jet_elements_composite_amounts_hash.v'
ARCHIVES = [
    ('elements-stream', 'jet_sha_hash_words_reader'),
    ('elements-stream', 'jet_elements_words_hash_program'),
    ('elements-annexes', 'jet_sha_hash_elems_reader'),
    ('elements-nonces', 'jet_sha_tagged_word_spec'),
    ('elements-nonces', 'jet_elements_nonce_hash_spec'),
    ('elements-nonces', 'jet_elements_nonces_hash_program'),
    ('elements-amounts-hash', 'jet_elements_asset_amount_hash_spec'),
    ('elements-amounts-hash', 'jet_elements_amounts_hash_program'),
    ('elements-composite-amounts', 'jet_elements_composite_amounts_hash'),
]
KERNEL = ['bash', '-c', 'ulimit -s 65520; exec bash build-jets.sh --coqchk -silent -o ' + MODULE]


def tree(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('distinct private tree required')
    # Tests are not the production implementation. Do not authorize any other
    # deviation from the starting C/Haskell/original-Coq specification target.
    subprocess.run(['git', 'diff', '--quiet', '91d89bac', '--', 'C', 'Haskell',
                    'Coq/Simplicity', ':(exclude)C/test.c'], cwd=s.REPO, check=True)
    for name, digest in s.input_map().items():
        if s.sha((work / name).read_bytes()) != digest:
            raise ValueError('current inherited source/input differs: ' + name)
    expected = {name[4:] for name in s.input_map() if name.startswith('Coq/')}
    for folder, stem in ARCHIVES:
        path = work / 'Coq/C' / (stem + '.v')
        if path.is_symlink() or path.read_bytes() != (HERE.parent / folder / 'source' / (stem + '.v.source')).read_bytes():
            raise ValueError('private/archive proof differs: ' + stem)
        s.safe_source(path.read_text(), stem)
        expected.add('C/' + stem + '.v')
    if g.inventory(work / 'Coq') != expected:
        raise ValueError('unexpected proof source or verification input')


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('compile receipt already exists')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    deps = Path(s.ENV['COMPCERT']).parent
    flags = []
    for name in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(Path(s.ENV['COMPCERT']) / name), 'compcert.' + name]
    flags += ['-R', str(Path(s.ENV['COMPCERT']) / 'flocq'), 'Flocq']
    for name in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(deps / 'vst-2.14' / name), 'VST.' + name]
    flags += ['-Q', str(deps / 'vst-2.14/sha'), 'sha']
    # The existing manifests remain byte-identical. Additional proof roots are
    # command-line arguments, with the project's unchanged compiler/load paths.
    extras = ['C/' + name + '.v' for _, name in ARCHIVES]
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-f', '_CoqProject.jets', *extras,
        *flags, '-o', 'CompositeProofMakefile'], 'makefile', 60)
    commands['build'] = s.run(work, ['make', '-f', 'CompositeProofMakefile', '-j2',
        NEW.removesuffix('.v') + '.vo'], 'build', 1800)
    commands['fresh'] = s.run(work, ['bash', 'build-jets.sh', '--coqc', '-q', NEW], 'fresh', 60)
    results, definitions, deps = g.reports(work, [(MODULE, work / 'Coq' / NEW)], 'composite', commands)
    expected = {name: {'FunctionalExtensionality.functional_extensionality_dep'} for name in results}
    closed = [name for name in results if name.endswith('_parametric')]
    endpoints = [name for name in results if name.endswith('_program_local_spec')]
    expected.update({name: set() for name in closed})
    expected.update({name: s.SIX for name in endpoints})
    if (len(results), len(definitions), len(closed), len(endpoints)) != (8, 5, 3, 2) or deps != expected:
        raise ValueError('unexpected complete result/type/dependency inventory')
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('verification changed main/index')
    record = dict(candidate=str(work), starting_revision='91d89bac',
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        main_inputs=before, staged_patch_sha256=index, commands=commands,
        results=results, definitions=definitions, endpoints=endpoints,
        dependencies={name: sorted(ds) for name, ds in deps.items()},
        sources_sha256={name: s.sha((work / 'Coq/C' / (name + '.v')).read_bytes()) for _, name in ARCHIVES},
        objects_sha256={name: s.sha((work / 'Coq/C' / (name + '.vo')).read_bytes()) for _, name in ARCHIVES},
        tools_sha256={'verify.py': s.sha(Path(__file__).read_bytes())},
        current_dependency_closure_rebuilt=True, historical_acceptance_reused=False,
        caller_cached_hashes_established=False, recursive_kernel_check=False,
        normal_registration=False, coverage_added=0, full_acceptance=False)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
               **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Both current-target C endpoints freshly compiled; full types and assumptions checked', flush=True)


def kernel(work):
    if (HERE / 'KERNEL-RUN.json').exists():
        raise ValueError('kernel already launched; inspect its original process/terminal')
    r = json.loads((HERE / 'RUN.json').read_text())
    tree(work)
    if (r['candidate'] != str(work) or r['main_inputs'] != s.input_map() or
        r['staged_patch_sha256'] != s.index_hash() or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work) or
        r['tools_sha256'] != {'verify.py': s.sha(Path(__file__).read_bytes())}):
        raise ValueError('compile identity differs')
    for field, suffix in [('sources_sha256', '.v'), ('objects_sha256', '.vo')]:
        for name, digest in r[field].items():
            if s.sha((work / 'Coq/C' / (name + suffix)).read_bytes()) != digest:
                raise ValueError('checked source/object changed')
    launch = dict(candidate=str(work), command=KERNEL, compile_sha256=s.sha((HERE / 'RUN.json').read_bytes()),
                  candidate_input_sha256=r['candidate_input_sha256'], recursive_kernel_check=False)
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
    print('Both current-target C endpoints recursively kernel-checked; normal admission remains separate', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['compile', 'kernel']:
        raise ValueError('usage: verify.py compile|kernel PRIVATE_TREE')
    globals()[sys.argv[1]](Path(sys.argv[2]).resolve())
