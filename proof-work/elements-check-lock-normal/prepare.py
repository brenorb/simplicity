"""Check the whole five-jet timelock family under final C module names."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('check_lock_normal_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-check-lock/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
if work in [base, REPO] or REPO in work.parents or (work / 'Coq').exists():
    raise ValueError('use a fresh external final-name preparation tree')
subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-check-lock/review.py')], check=True)
if support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
    raise ValueError('checked check-lock source base changed')
before, index = support.input_map(), support.index_hash()
subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
for name in ['C', 'Haskell']:
    (work / name).symlink_to(REPO / name, target_is_directory=True)
coq = work / 'Coq'
if support.inputs.fingerprint(coq, work) != prior['candidate_input_sha256']:
    raise ValueError('copied inherited source differs')
new_sources = ['C/jet_application_partial_transport.v', 'C/jet_elements_check_lock_literal.v']
changes = {}
for name in new_sources:
    text = (HERE.parent / 'elements-check-lock/source' / (Path(name).name + '.source')).read_text()
    if name.endswith('jet_elements_check_lock_literal.v'):
        old = 'Require Import CheckLockReview.jet_application_partial_transport.'
        if text.count(old) != 1:
            raise ValueError('unexpected partial-transport namespace boundary')
        text = text.replace(old, 'Require Import C.jet_application_partial_transport.')
    support.safe_source(text, name)
    if (coq / name).exists():
        raise ValueError('final-name target already exists')
    changes[coq / name] = text
support.changed(changes)
fingerprint = support.inputs.fingerprint(coq, work)
roots = ['C.jet_elements_is_final_local', 'C.jet_elements_lock_literal', 'C.jet_elements_check_lock_literal']
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic final-name assertion dependency')
    visiting.add(module)
    code = support.safe_source((coq / (module.replace('.', '/') + '.v')).read_text(), module)
    for declaration in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dep in declaration.split():
            if dep.startswith('C.'):
                visit(dep)
    visiting.remove(module)
    seen.add(module)
    if module.replace('.', '/') + '.v' not in manifest:
        order.append(module)


for root in roots:
    visit(root)
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh final-name assertion/timelock closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
results, definitions = [], []
for module in order:
    code = support.safe_source((coq / (module.replace('.', '/') + '.v')).read_text(), module)
    results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
    definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
references = ['C.jet_elements_sequence_literal.application_jet_local_spec_sep_pointwise']
driver = ['Require ' + ' '.join(order) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + references:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "CHECK_LOCK_NORMAL_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
pure = ['C.jet_elements_lock_literal.elements_parse_lock_literal_matches',
        'C.jet_elements_lock_literal.elements_lock_literal_program_matches',
        'C.jet_elements_check_lock_literal.elements_check_lock_literal_program_matches']
original_deps = {n.replace('CheckLockReview.', 'C.', 1): ds for n, ds in prior['dependencies'].items()}
if (set(deps) != set(results + references) or any(not ds <= support.SIX for ds in deps.values()) or
        any(deps[n] for n in pure) or any(sorted(ds) != original_deps[n] for n, ds in deps.items())):
    raise ValueError('new/nonclosed final-name bridge or inherited dependency mismatch')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^CHECK_LOCK_NORMAL_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete final-name assertion contract reports')
literal, transport = new_sources[1], new_sources[0]
run([sys.executable, '-B', str(HERE.parent / 'elements-check-lock/check-source.py'), '--repo', str(work),
     '--coq', '.', '--literal', literal, '--transport', transport], 'source')
run([sys.executable, '-B', str(HERE.parent / 'elements-check-lock/test-source.py'), str(work), '.', literal, transport], 'source-negative')
for package in ['elements-finality', 'elements-lock']:
    positional = [] if package == 'elements-finality' else ['C/jet_elements_lock_literal.v']
    run([sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.', *positional], package + '-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or
        support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/candidate/base source drift during final-name preparation')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'base_input_sha256': prior['candidate_input_sha256'], 'candidate_input_sha256': fingerprint,
          'main_inputs': before, 'staged_patch_sha256': index, 'roots': roots, 'new_sources': new_sources,
          'missing_dependency_modules': order, 'results': results, 'definitions': definitions,
          'reference_results': references, 'pure_results': pure,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'object_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'tools_sha256': {'prepare.py': support.sha(Path(__file__).read_bytes()),
                          **{package + '/' + n: support.sha((HERE.parent / package / n).read_bytes())
                             for package, names in [('elements-check-lock', ['check-source.py', 'test-source.py']),
                                                    ('elements-finality', ['test-source.py']),
                                                    ('elements-lock', ['test-source.py'])] for n in names}},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
archives = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for name in new_sources:
    archives[HERE / 'source' / (Path(name).name + '.source')] = (coq / name).read_text()
for name in ['assumptions.log', 'contracts.log', 'ast.log', 'kernel.log']:
    archives[HERE / name] = (work / name).read_text()
support.changed(archives)
print('Five timelock/assertion C contracts checked under final C names; no normal registration claimed', flush=True)
