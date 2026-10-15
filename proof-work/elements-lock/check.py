"""Fresh lock-jet/literal-source checks on an already isolated source copy."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('lock_proof_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-finality/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
coq, literal = work / 'Coq', work / 'Proof/jet_elements_lock_literal.v'
if work == base or work == REPO or REPO in work.parents:
    raise ValueError('lock checks require an independent external tree')
before, index = support.input_map(), support.index_hash()
fingerprint = support.inputs.fingerprint(coq, work)
if (fingerprint != prior['candidate_input_sha256'] or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('lock check inherited source copy differs from checked finality base')
literal_source = literal.read_text()
support.safe_source(literal_source, str(literal))
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic lock-proof dependency')
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


for root in ['C.jet_elements_lock_local', 'C.jet_elements_sequence_literal', 'C.jet_haskell_word_conversion']:
    visit(root)
flags = ['-Q', str(work / 'Proof'), 'LockLiteral']
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh lock dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(literal)], 'literal')
literal_module = 'LockLiteral.jet_elements_lock_literal'
modules = order + [literal_module]
results, definitions = [], []
for module in modules:
    path = literal if module == literal_module else coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(path.read_text(), module)
    results += [module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary)\s+(\w+)', code, re.M)]
    definitions += [module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
driver = ['Require ' + ' '.join(modules) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "LOCK_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
pure = [literal_module + '.' + n for n in ['elements_parse_lock_literal_matches', 'elements_lock_literal_program_matches']]
if set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure):
    raise ValueError('unreviewed lock assumptions or nonclosed literal bridges')
for suffix in ['height', 'time']:
    if deps[literal_module + '.elements_tx_lock_' + suffix + '_literal_local_spec'] != deps[
            'C.jet_elements_lock_local.elements_tx_lock_' + suffix + '_local_spec']:
        raise ValueError('literal C endpoint changed original assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^LOCK_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete deep lock records')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.', '--literal', str(literal)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal)], 'source-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
run(['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', 'C.jet_elements_lock_local', literal_module], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or literal.read_text() != literal_source or
        support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/candidate/base source drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'LockLiteral',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'candidate_input_sha256': fingerprint, 'main_inputs': before, 'staged_patch_sha256': index,
          'fresh_modules': order, 'modules': modules, 'results': results, 'definitions': definitions,
          'pure_results': pure, 'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha((literal if m == literal_module else coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in modules},
          'object_sha256': {m: support.sha((literal if m == literal_module else coq / (m.replace('.', '/') + '.v')).with_suffix('.vo').read_bytes()) for m in modules},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
archives = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for name in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
    archives[HERE / name] = (work / name).read_text()
for module in modules:
    path = literal if module == literal_module else coq / (module.replace('.', '/') + '.v')
    archives[HERE / 'source' / (module.split('.')[-1] + '.v.source')] = path.read_text()
support.changed(archives)
print('Both actual-C lock jets pass literal-source, full-compilation and recursive-kernel checks; normal registration remains pending', flush=True)
