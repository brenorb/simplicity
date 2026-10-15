"""Check finality/lock proofs under final C names, without changing main.

Only source metadata is read from the live direct-getter candidate. Compiler
objects come from the immutable checked lock tree, never a running audit.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('timelock_normal_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
direct_path = HERE.parent / 'elements-direct-getters-admission/REVIEW.json'
direct = json.loads(direct_path.read_text())
base = Path(direct['review']['candidate'])
lock_path = HERE.parent / 'elements-lock/PREPARATION.json'
lock = json.loads(lock_path.read_text())
objects = Path(lock['candidate'])
if work in [base, objects, REPO] or REPO in work.parents or (work / 'Coq').exists():
    raise ValueError('use a fresh independent external preparation tree')
for package in ['elements-finality', 'elements-lock']:
    subprocess.run([sys.executable, '-B', str(HERE.parent / package / 'review.py')], check=True)
if support.inputs.fingerprint(base / 'Coq', base) != direct['candidate_input_sha256']:
    raise ValueError('reviewed direct-getter source base changed')
before, index = support.input_map(), support.index_hash()
subprocess.run(['cp', '-cR', str(objects / 'Coq'), str(work / 'Coq')], check=True)
for name in ['C', 'Haskell']:
    (work / name).symlink_to(REPO / name, target_is_directory=True)
coq = work / 'Coq'
# Reconstruct the reviewed source baseline using static inputs only. Do not
# copy a .vo or any other mutable output from the running direct-getter audit.
overlay = ['_CoqProject', '_CoqProject.jets', 'C/jet_public_theorems.txt',
           'C/jet_contract_definitions.txt', 'C/jet_coverage.tsv',
           'C/jet_assumptions.expected', 'C/jet_contracts.expected',
           'jet-coverage.py', 'test-jet-coverage.py', 'check-jets.sh', 'audit-jet-contracts.sh']
overlay += [directory + '/' + name for directory in ['elements-tapleaf-literal', 'elements-hash-literal']
            for name in ['check-source.py', 'test-source.py']]
support.changed({coq / n: (base / 'Coq' / n).read_text() for n in overlay})
if support.inputs.fingerprint(coq, work) != direct['candidate_input_sha256']:
    raise ValueError('reconstructed source baseline is not byte-identical')
new_source = 'C/jet_elements_lock_literal.v'
literal = coq / new_source
archive = HERE.parent / 'elements-lock/source/jet_elements_lock_literal.v.source'
support.safe_source(archive.read_text(), str(archive))
if literal.exists():
    raise ValueError('literal target already exists')
support.changed({literal: archive.read_text()})
fingerprint = support.inputs.fingerprint(coq, work)
roots = ['C.jet_elements_is_final_local', 'C.jet_elements_lock_literal']
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic timelock dependency')
    visiting.add(module)
    source = coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(source.read_text(), module)
    for declaration in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in declaration.split():
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


print('Fresh final-name timelock dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
results, definitions = [], []
for module in order:
    code = support.safe_source((coq / (module.replace('.', '/') + '.v')).read_text(), module)
    results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
    definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
driver = ['Require ' + ' '.join(order) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "TIMELOCK_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
pure = ['C.jet_elements_lock_literal.' + n for n in ['elements_parse_lock_literal_matches', 'elements_lock_literal_program_matches']]
if set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure):
    raise ValueError('new final-name assumptions/nonclosed source bridges')
for suffix in ['height', 'time']:
    if deps['C.jet_elements_lock_literal.elements_tx_lock_' + suffix + '_literal_local_spec'] != deps[
            'C.jet_elements_lock_local.elements_tx_lock_' + suffix + '_local_spec']:
        raise ValueError('final-name endpoint changed original assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TIMELOCK_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete final-name type/definition report')
for package in ['elements-finality', 'elements-lock']:
    flags = [] if package == 'elements-finality' else ['--literal', new_source]
    positional = [] if package == 'elements-finality' else [new_source]
    run([sys.executable, '-B', str(HERE.parent / package / 'check-source.py'), '--repo', str(work), '--coq', '.', *flags], package + '-source')
    run([sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.', *positional], package + '-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or
        literal.read_bytes() != archive.read_bytes() or support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != direct['candidate_input_sha256']):
    raise ValueError('main/index/candidate/source-base drift during final-name check')
record = {'candidate': str(work), 'base_candidate': str(base), 'object_base_candidate': str(objects),
          'base_review_sha256': support.sha(direct_path.read_bytes()),
          'object_base_preparation_sha256': support.sha(lock_path.read_bytes()),
          'base_input_sha256': direct['candidate_input_sha256'], 'candidate_input_sha256': fingerprint,
          'main_inputs': before, 'staged_patch_sha256': index, 'source_overlay': overlay,
          'namespace': 'C', 'roots': roots, 'new_sources': [new_source], 'missing_dependency_modules': order,
          'results': results, 'definitions': definitions, 'pure_results': pure,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'object_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'tools_sha256': {'prepare.py': support.sha(Path(__file__).read_bytes()),
                          **{p + '/' + n: support.sha((HERE.parent / p / n).read_bytes())
                             for p in ['elements-finality', 'elements-lock'] for n in ['check-source.py', 'test-source.py']}},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
archives = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n',
            HERE / 'source/jet_elements_lock_literal.v.source': literal.read_text()}
for name in ['assumptions.log', 'contracts.log', 'kernel.log', 'ast.log']:
    archives[HERE / name] = (work / name).read_text()
support.changed(archives)
print('Three timelock jet contracts checked under final C names; registration/full acceptance not claimed', flush=True)
