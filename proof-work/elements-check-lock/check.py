"""Check both check-lock C jets and reusable failure-preserving transport."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('check_lock_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-timelock-normal/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
coq = work / 'Coq'
if work in [base, REPO] or REPO in work.parents:
    raise ValueError('check-lock work requires a distinct external copy')
before, index = support.input_map(), support.index_hash()
fingerprint = support.inputs.fingerprint(coq, work)
if (fingerprint != prior['candidate_input_sha256'] or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('check-lock inherited source copy differs')
proof_modules = ['CheckLockReview.jet_application_partial_transport', 'CheckLockReview.jet_elements_check_lock_literal']
paths = {m: work / 'Proof' / (m.split('.')[-1] + '.v') for m in proof_modules}
proof_sources = {m: p.read_text() for m, p in paths.items()}
for m, source in proof_sources.items():
    support.safe_source(source, m)
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic check-lock dependency')
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


for module in ['C.jet_elements_check_lock', 'C.jet_elements_lock_literal']:
    visit(module)
paths.update({m: coq / (m.replace('.', '/') + '.v') for m in order})
flags = ['-Q', str(work / 'Proof'), 'CheckLockReview']
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh check-lock dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
for module in proof_modules:
    run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(paths[module])], module)
modules = order + proof_modules
results, definitions = [], []
for module in modules:
    code = support.safe_source(paths[module].read_text(), module)
    results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
    definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
references = ['C.jet_elements_sequence_literal.application_jet_local_spec_sep_pointwise']
driver = ['Require ' + ' '.join(modules) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + references:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "CHECK_LOCK_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
pure = [proof_modules[1] + '.elements_check_lock_literal_program_matches']
transport_name = proof_modules[0] + '.application_jet_partial_spec_pointwise'
if (set(deps) != set(results + references) or any(not ds <= support.SIX for ds in deps.values()) or
        any(deps[n] for n in pure) or deps[transport_name] != deps[references[0]]):
    raise ValueError('unreviewed check-lock assumptions/nonclosed bridges')
for suffix in ['height', 'time']:
    if deps[proof_modules[1] + '.elements_check_lock_' + suffix + '_literal_local_spec'] != deps[
            'C.jet_elements_check_lock.elements_check_lock_' + suffix + '_local_spec']:
        raise ValueError('literal check-lock assumptions differ from original')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^CHECK_LOCK_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete check-lock reports')
literal, transport = paths[proof_modules[1]], paths[proof_modules[0]]
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.',
     '--literal', str(literal), '--transport', str(transport)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal), str(transport)], 'source-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
roots = ['C.jet_elements_check_lock', *proof_modules]
run(['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or
        any(paths[m].read_text() != source for m, source in proof_sources.items()) or
        support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/candidate/source-base drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'CheckLockReview',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'candidate_input_sha256': fingerprint, 'main_inputs': before, 'staged_patch_sha256': index,
          'fresh_modules': order, 'proof_modules': proof_modules, 'roots': roots,
          'results': results, 'definitions': definitions, 'pure_results': pure, 'reference_results': references,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha(paths[m].read_bytes()) for m in modules},
          'object_sha256': {m: support.sha(paths[m].with_suffix('.vo').read_bytes()) for m in modules},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for name in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
    changes[HERE / name] = (work / name).read_text()
for m in modules:
    changes[HERE / 'source' / (m.split('.')[-1] + '.v.source')] = paths[m].read_text()
support.changed(changes)
print('Both check-lock C jets and failure-preserving transport checked through full compile, source, AST and recursive kernel gates; no registration claimed', flush=True)
