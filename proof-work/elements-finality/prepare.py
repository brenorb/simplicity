"""Freshly check existing actual-C TxIsFinal proof in a private normal tree."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('finality_prep_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-direct-getters-normal/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
if (work == base or work == REPO or REPO in work.parents or (work / 'Coq').exists()):
    raise ValueError('use a fresh external directory')
if support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
    raise ValueError('immutable final-name source base changed')
before, index = support.input_map(), support.index_hash()
subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
for name in ['C', 'Haskell']:
    (work / name).symlink_to(REPO / name, target_is_directory=True)
coq = work / 'Coq'
fingerprint = support.inputs.fingerprint(coq, work)
if fingerprint != prior['candidate_input_sha256']:
    raise ValueError('private copied source differs')
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
visited, visiting, order = set(), set(), []
roots = ['C.jet_elements_is_final_spec', 'C.jet_elements_is_final_local']


def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise ValueError('cyclic finality proof dependency')
    visiting.add(module)
    source = coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(source.read_text(), str(source))
    for declaration in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in declaration.split():
            if dependency.startswith('C.'):
                visit(dependency)
    visiting.remove(module)
    visited.add(module)
    if module in roots or module.replace('.', '/') + '.v' not in manifest:
        order.append(module)


for module in roots:
    visit(module)
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh finality dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
results, definitions = [], []
for module in order:
    source = coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(source.read_text(), str(source))
    results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
    definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
driver = ['Require ' + ' '.join(order) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "FINALITY_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()):
    raise ValueError('unexpected finality result assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^FINALITY_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete finality contracts')
for stem, command in [
    ('source', [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.']),
    ('source-negative', [sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.']),
]:
    run(command, stem)
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or
        support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/base/candidate source drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'roots': roots,
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'candidate_input_sha256': fingerprint, 'base_input_sha256': prior['candidate_input_sha256'],
          'main_inputs': before, 'staged_patch_sha256': index,
          'fresh_modules': order, 'results': results, 'definitions': definitions,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'sources_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'objects_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['prepare.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for name in ['contracts.log', 'assumptions.log', 'kernel.log', 'source.log', 'source-negative.log']:
    changes[HERE / name] = (work / name).read_text()
for module in order:
    changes[HERE / 'source' / (module.removeprefix('C.') + '.v.source')] = (coq / (module.replace('.', '/') + '.v')).read_text()
support.changed(changes)
print('Actual-C TxIsFinal source, fresh compilation and recursive kernel checks passed; no registration claimed', flush=True)
