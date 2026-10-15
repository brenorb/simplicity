"""Check indexed/current pegin proofs under their final C module name."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('normal_pegin_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-pegin/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
if work in [base, REPO] or REPO in work.parents or (work / 'Coq').exists():
    raise ValueError('use a fresh external final-name tree')
subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-pegin/review.py')], check=True)
before, index = support.input_map(), support.index_hash()
if support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
    raise ValueError('checked pegin source base changed')
subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
for name in ['C', 'Haskell']:
    (work / name).symlink_to(REPO / name, target_is_directory=True)
coq = work / 'Coq'
if support.inputs.fingerprint(coq, work) != prior['candidate_input_sha256']:
    raise ValueError('copied inherited source differs')
new_source = 'C/jet_elements_pegin_literal.v'
archive = HERE.parent / 'elements-pegin/source/jet_elements_pegin_literal.v.source'
support.safe_source(archive.read_text(), str(archive))
if (coq / new_source).exists():
    raise ValueError('final pegin source already exists')
support.changed({coq / new_source: archive.read_text()})
fingerprint = support.inputs.fingerprint(coq, work)
roots = ['C.jet_elements_pegin_local', 'C.jet_elements_current_gen_jets', 'C.jet_elements_pegin_literal']
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic final-name pegin dependency')
    visiting.add(module)
    code = support.safe_source((coq / (module.replace('.', '/') + '.v')).read_text(), module)
    for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in block.split():
            if dependency.startswith('C.'):
                visit(dependency)
    visiting.remove(module)
    seen.add(module)
    if module.replace('.', '/') + '.v' not in manifest:
        order.append(module)


for root in roots:
    visit(root)
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh final-name pegin closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
results, definitions = [], []
for m in order:
    code = support.safe_source((coq / (m.replace('.', '/') + '.v')).read_text(), m)
    results += [m + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
    definitions += [m + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
driver = ['Require ' + ' '.join(order) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for n in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for n in names:
        contracts += ['Goal True. idtac "NORMAL_PEGIN_' + kind + ' ' + n + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
old_deps = {n.replace('PeginLiteral.', 'C.', 1): ds for n, ds in prior['dependencies'].items()}
if (set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or
        any(sorted(ds) != old_deps[n] for n, ds in deps.items())):
    raise ValueError('namespace rebasing introduced assumption changes')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^NORMAL_PEGIN_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete final-name pegin records')
run([sys.executable, '-B', str(HERE.parent / 'elements-pegin/check-source.py'), '--repo', str(work), '--coq', '.', '--literal', new_source], 'source')
run([sys.executable, '-B', str(HERE.parent / 'elements-pegin/test-source.py'), str(work), '.', new_source], 'source-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or
        (coq / new_source).read_bytes() != archive.read_bytes() or
        support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/candidate/source-base drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'base_input_sha256': prior['candidate_input_sha256'], 'candidate_input_sha256': fingerprint,
          'main_inputs': before, 'staged_patch_sha256': index, 'new_sources': [new_source], 'roots': roots,
          'missing_dependency_modules': order, 'results': results, 'definitions': definitions,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'object_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'tools_sha256': {'prepare.py': support.sha(Path(__file__).read_bytes()),
                          **{n: support.sha((HERE.parent / 'elements-pegin' / n).read_bytes()) for n in ['check-source.py', 'test-source.py']}},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n',
           HERE / 'source/jet_elements_pegin_literal.v.source': (coq / new_source).read_text()}
for n in ['assumptions.log', 'contracts.log', 'ast.log', 'kernel.log']:
    changes[HERE / n] = (work / n).read_text()
support.changed(changes)
print('Both pegin C contracts checked under final C names; normal registration not claimed', flush=True)
