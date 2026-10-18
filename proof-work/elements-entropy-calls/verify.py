"""Force-build the entropy proof port for the exact original Elements AST."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('entropy_port', HERE / 'port.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s, g, b = p.s, p.g, p.b
ROOTS = [p.ROOT, 'C.jet_elements_sha_program']


def tree(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('distinct private proof tree required')
    inputs = s.input_map()
    for name, digest in inputs.items():
        file = work / name
        if name == b.ALIAS:
            if file.is_symlink() or file.read_bytes() != (s.REPO / b.TARGET).read_bytes():
                raise ValueError('proof-loading alias differs from original target AST')
        elif s.sha(file.read_bytes()) != digest:
            raise ValueError('inherited source differs: ' + name)
    expected = {n[4:] for n in inputs if n.startswith('Coq/')}
    for n in b.NAMES:
        file = work / 'Coq/C' / (n + '.v')
        if file.is_symlink() or file.read_bytes() != (b.HERE / 'source' / (n + '.v.source')).read_bytes():
            raise ValueError('inherited calculation support differs: ' + n)
        expected.add('C/' + n + '.v')
    actual = {n: (work / 'Coq/C' / (n + '.v')).read_text() for n in p.NAMES + [p.MODEL]}
    p.check(actual)
    if actual != {f.name.removesuffix('.v.source'): f.read_text() for f in (HERE / 'source').glob('*.v.source')}:
        raise ValueError('entropy private/archive source differs')
    expected.update('C/' + n + '.v' for n in actual)
    if g.inventory(work / 'Coq') != expected:
        raise ValueError('unexpected entropy source inventory')


def compile(work):
    if (HERE / 'LAUNCH.json').exists():
        raise ValueError('entropy build already launched; inspect its original process')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    s.changed({HERE / 'LAUNCH.json': json.dumps(dict(candidate=str(work), roots=ROOTS,
        main_inputs_sha256=s.sha(json.dumps(before, sort_keys=True).encode()),
        staged_patch_sha256=index, compile_complete=False, recursive_kernel_check=False), indent=2) + '\n'})
    flags = []
    for n in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(Path(s.ENV['COMPCERT']) / n), 'compcert.' + n]
    flags += ['-R', str(Path(s.ENV['COMPCERT']) / 'flocq'), 'Flocq']
    runtime = Path(s.ENV['COMPCERT']).parent
    for n in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(runtime / 'vst-2.14' / n), 'VST.' + n]
    flags += ['-Q', str(runtime / 'vst-2.14/sha'), 'sha']
    extras = set()
    for root in ROOTS:
        g.LM = root
        extras.update(n.replace('.', '/') + '.v' for n in g.closure(work / 'Coq'))
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-f', '_CoqProject.jets',
        *sorted(extras), *flags, '-o', 'EntropyMakefile'], 'entropy-makefile', 60)
    print('Forcing the entropy helper and its entire original-program local source closure', flush=True)
    commands['build'] = s.run(work, ['make', '-f', 'EntropyMakefile', '-B', '-j2',
        *(n.replace('.', '/') + '.vo' for n in ROOTS)], 'entropy-build', 5400)
    names = p.NAMES + [p.MODEL]
    modules = [('C.' + n, work / 'Coq/C' / (n + '.v')) for n in names]
    modules += [('C.jet_elements_sha_program', work / 'Coq/C/jet_elements_sha_program.v')]
    results, definitions, deps = g.reports(work, modules, 'entropy', commands)
    if any(deps['C.jet_elements_sha_program.' + n] for n in ['elements_sha_program', 'elements_sha_genv']):
        raise ValueError('original target program/genv equality is not closed')
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('entropy compile changed main inputs or staging')
    record = dict(candidate=str(work), starting_revision='91d89bac', main_inputs=before,
        staged_patch_sha256=index, commands=commands, roots=ROOTS,
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        proof_loading_aliases={b.ALIAS: b.TARGET},
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['verify.py', 'port.py']},
        force_rebuilt_entire_local_closure=True, recursive_kernel_check=False,
        exact_per_result_profile_review=False, helper_register_formula_only=True,
        canonical_word_bridge_proved=False, public_frame_jet_lifecycle_proved=False,
        normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(record, indent=2) + '\n',
        HERE / 'build.log': (work / 'entropy-build.log').read_text(),
        **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text()
           for stem in ['entropy-makefile', 'entropy-assumptions', 'entropy-contracts']}})
    force = s.load('entropy_force_closure', HERE.parent / 'verify-forced-closure.py')
    force.snapshot(HERE, ROOTS)
    print('Entropy helper proof port compiled with full reports and forced-source closure; word bridge and jet body remain open', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'compile':
        raise ValueError('usage: verify.py compile PRIVATE_TREE')
    compile(Path(sys.argv[2]).resolve())
