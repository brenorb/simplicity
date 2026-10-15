"""Freshly verify two pegin C contracts using shared index/digest bridges."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('pegin_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-check-lock-normal/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
coq, literal = work / 'Coq', work / 'Proof/jet_elements_pegin_literal.v'
if work in [base, REPO] or REPO in work.parents:
    raise ValueError('pegin proof checks require a distinct external tree')
before, index = support.input_map(), support.index_hash()
fingerprint = support.inputs.fingerprint(coq, work)
if fingerprint != prior['candidate_input_sha256'] or support.inputs.fingerprint(base / 'Coq', base) != fingerprint:
    raise ValueError('pegin inherited source copy differs')
literal_source = literal.read_text()
support.safe_source(literal_source, str(literal))
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(module):
    if module in seen:
        return
    if module in visiting:
        raise ValueError('cyclic pegin dependency')
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


for module in ['C.jet_elements_pegin_local', 'C.jet_elements_current_gen_jets']:
    visit(module)
commands = {}
flags = ['-Q', str(work / 'Proof'), 'PeginLiteral']


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh pegin C dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(literal)], 'literal')
literal_module = 'PeginLiteral.jet_elements_pegin_literal'
modules = order + [literal_module]
paths = {m: literal if m == literal_module else coq / (m.replace('.', '/') + '.v') for m in modules}
results, definitions = [], []
for m, path in paths.items():
    code = support.safe_source(path.read_text(), m)
    results += [m + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
    definitions += [m + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
driver = ['Require ' + ' '.join(modules) + '.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "PEGIN_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', *flags, str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
originals = ['C.jet_elements_pegin_local.elements_input_pegin_hash_local_spec',
             'C.jet_elements_current_gen_jets.elements_current_pegin_local_spec']
finals = [literal_module + '.elements_' + p + '_pegin_literal_local_spec' for p in ['input', 'current']]
if set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()) or any(deps[a] != deps[b] for a, b in zip(finals, originals)):
    raise ValueError('new/unreviewed pegin assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^PEGIN_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete pegin contract report')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', '.', '--literal', str(literal)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(work), '.', str(literal)], 'source-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
roots = ['C.jet_elements_pegin_local', 'C.jet_elements_current_gen_jets', literal_module]
run(['bash', 'build-jets.sh', '--coqchk', *flags, '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or literal.read_text() != literal_source or
        support.inputs.fingerprint(coq, work) != fingerprint or support.inputs.fingerprint(base / 'Coq', base) != fingerprint):
    raise ValueError('main/index/candidate/source-base drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'PeginLiteral',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()),
          'candidate_input_sha256': fingerprint, 'main_inputs': before, 'staged_patch_sha256': index,
          'fresh_modules': order, 'literal_module': literal_module, 'roots': roots,
          'results': results, 'definitions': definitions, 'originals': originals, 'finals': finals,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha(path.read_bytes()) for m, path in paths.items()},
          'object_sha256': {m: support.sha(path.with_suffix('.vo').read_bytes()) for m, path in paths.items()},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for name in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
    changes[HERE / name] = (work / name).read_text()
for m, path in paths.items():
    changes[HERE / 'source' / (m.split('.')[-1] + '.v.source')] = path.read_text()
support.changed(changes)
print('Both actual-C pegin contracts checked through source, full compile, exact AST and recursive kernel gates; no registration claimed', flush=True)
