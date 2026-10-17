"""Recheck existing calculation helpers for the exact original Elements AST.

Only a private proof-loading alias differs from main: jets_sha.v is byte-for-
byte jets_elements.v. The original-program/genv equality is a checked root.
No C input, original specification or generation setting is changed.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('calculation_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)
g = s.load('calculation_reports', HERE.parent / 'elements-tap-getters/check.py')
NAMES = ['jet_elements_calc_field_eval', 'jet_elements_calculate_asset_exec',
         'jet_elements_calculate_token_exec', 'jet_env_store_words',
         'jet_elements_sha_program', 'jet_elements_issuance_calc_spec', 'jet_elements_calc_registers']
ROOTS = ['C.jet_elements_calculate_token_exec', 'C.jet_elements_sha_program', 'C.jet_elements_calc_registers']
ALIAS = 'Coq/C/jets_sha.v'
TARGET = 'Coq/C/jets_elements.v'


def tree(work):
    if work == s.REPO or s.REPO in work.parents or (work / 'Coq').is_symlink():
        raise ValueError('distinct non-symlink private proof tree required')
    subprocess.run(['git', 'diff', '--quiet', '91d89bac', '--', 'C', 'Haskell',
                    'Coq/Simplicity', ':(exclude)C/test.c'], cwd=s.REPO, check=True)
    inputs = s.input_map()
    for name, digest in inputs.items():
        if name == ALIAS:
            if (work / name).is_symlink() or (work / name).read_bytes() != (s.REPO / TARGET).read_bytes():
                raise ValueError('alias must be an exact copy of the unchanged original target AST')
        elif s.sha((work / name).read_bytes()) != digest:
            raise ValueError('inherited input differs: ' + name)
    expected = {n[4:] for n in inputs if n.startswith('Coq/')}
    for n in NAMES:
        p = work / 'Coq/C' / (n + '.v')
        if p.is_symlink() or p.read_bytes() != (HERE / 'source' / (n + '.v.source')).read_bytes():
            raise ValueError('proof/archive differs: ' + n)
        s.safe_source(p.read_text(), n)
        expected.add('C/' + n + '.v')
    if g.inventory(work / 'Coq') != expected:
        raise ValueError('unexpected source inventory')


def compile(work):
    if (HERE / 'RUN.json').exists():
        raise ValueError('basis receipt already exists; inspect its original run')
    tree(work)
    before, index = s.input_map(), s.index_hash()
    runtime = Path(s.ENV['COMPCERT']).parent
    flags = []
    for n in ['lib', 'common', 'x86_64', 'x86', 'cfrontend', 'export']:
        flags += ['-R', str(Path(s.ENV['COMPCERT']) / n), 'compcert.' + n]
    flags += ['-R', str(Path(s.ENV['COMPCERT']) / 'flocq'), 'Flocq']
    for n in ['msl', 'sepcomp', 'veric', 'zlist', 'floyd', 'progs64', 'concurrency', 'atomics']:
        flags += ['-Q', str(runtime / 'vst-2.14' / n), 'VST.' + n]
    flags += ['-Q', str(runtime / 'vst-2.14/sha'), 'sha']
    extras = set()
    for root in ROOTS:
        g.LM = root
        extras.update(n.replace('.', '/') + '.v' for n in g.closure(work / 'Coq'))
    commands = {}
    commands['makefile'] = s.run(work, ['coq_makefile', '-f', '_CoqProject.jets',
        *sorted(extras), *flags, '-o', 'CalculationBasisMakefile'], 'makefile', 60)
    commands['build'] = s.run(work, ['make', '-f', 'CalculationBasisMakefile', '-B', '-j2',
        *(n.replace('.', '/') + '.vo' for n in ROOTS)], 'build', 5400)
    modules = ['C.' + n for n in NAMES]
    results, definitions, deps = g.reports(work,
        [(m, work / 'Coq' / (m.replace('.', '/') + '.v')) for m in modules], 'basis', commands)
    for name in ['elements_sha_program', 'elements_sha_genv']:
        if deps['C.jet_elements_sha_program.' + name]:
            raise ValueError('program/genv equality must be closed')
    tree(work)
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('basis check changed main/index')
    r = dict(candidate=str(work), starting_revision='91d89bac', main_inputs=before,
        staged_patch_sha256=index, commands=commands, roots=ROOTS,
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        results=results, definitions=definitions, dependencies={n: sorted(d) for n, d in deps.items()},
        proof_loading_aliases={ALIAS: TARGET},
        proof_loading_alias_sha256=s.sha((work / ALIAS).read_bytes()),
        sources_sha256={n: s.sha((work / 'Coq/C' / (n + '.v')).read_bytes()) for n in NAMES},
        objects_sha256={n: s.sha((work / 'Coq/C' / (n + '.vo')).read_bytes()) for n in NAMES},
        tools_sha256={'basis.py': s.sha(Path(__file__).read_bytes())},
        force_rebuilt_entire_local_closure=True, recursive_kernel_check=False,
        exact_assumption_profile_review=False, whole_c_jet_equivalence_proved=False,
        public_frame_jet_lifecycle_proved=False, normal_registration=False, coverage_added=0)
    s.changed({HERE / 'RUN.json': json.dumps(r, indent=2) + '\n',
               **{HERE / (stem + '.log'): (work / (stem + '.log')).read_text() for stem in commands}})
    print('Original-program calculation helper basis compiled; full assumption review and recursive checking remain separate', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] != 'compile':
        raise ValueError('usage: basis.py compile PRIVATE_TREE')
    compile(Path(sys.argv[2]).resolve())
