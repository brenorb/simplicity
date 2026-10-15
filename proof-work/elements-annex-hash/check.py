"""Fresh C-to-annex-hash checks in an isolated final-name tree, without registration."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('annex_hash_check_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-pegin-normal/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
coq, literal = work / 'Coq', work / 'Coq/C/jet_elements_optional_digest_literal.v'
lm = 'C.jet_elements_optional_digest_literal'
if work == base or work == REPO or REPO in work.parents or (HERE / 'PREPARATION.json').exists():
    raise ValueError('use a distinct unchecked external tree')
subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-pegin-normal/review.py')], check=True)
before, index = support.input_map(), support.index_hash()
if support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
    raise ValueError('checked base changed')
base_sources = support.load('annex_hash_base_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
inherited = base_sources(base / 'Coq')
if base_sources(coq) != inherited | {'C/jet_elements_optional_digest_literal.v'}:
    raise ValueError('unexpected source inventory')
for name in inherited:
    if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
        raise ValueError('inherited source/metadata/registry drift: ' + name)
if literal.read_bytes() != (HERE / 'source/jet_elements_optional_digest_literal.v.source').read_bytes():
    raise ValueError('archive/proof differ')
fingerprint = support.inputs.fingerprint(coq, work)
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
seen, visiting, order = set(), set(), []


def visit(m):
    if m in seen:
        return
    if m in visiting:
        raise ValueError('cyclic annex-hash dependency')
    visiting.add(m)
    code = support.safe_source((coq / (m.replace('.', '/') + '.v')).read_text(), m)
    for block in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in block.split():
            if dependency.startswith('C.'):
                visit(dependency)
    visiting.remove(m)
    seen.add(m)
    if m.replace('.', '/') + '.v' not in manifest:
        order.append(m)


visit(lm)
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


print('Fresh annex-hash closure: ' + ', '.join(order), flush=True)
for m in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'], m)
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
        contracts += ['Goal True. idtac "ANNEX_HASH_' + kind + ' ' + n + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if set(deps) != set(results) or any(not ds <= support.SIX for ds in deps.values()):
    raise ValueError('incomplete or unreviewed assumptions')
for n, ds in deps.items():
    if not n.startswith((lm + '.', 'C.jet_elements_annex_local.')) and sorted(ds) != prior['dependencies'][n]:
        raise ValueError('inherited dependency set changed')
pure = [lm + '.elements_input_optional_digest_literal_matches', lm + '.elements_pegin_literal_uses_optional_digest']
if any(deps[n] for n in pure):
    raise ValueError('generic optional conversion/pegin compatibility is not closed')
originals = ['C.jet_elements_annex_local.elements_input_annex_hash_local_spec',
             'C.jet_elements_current_gen_jets.elements_current_annex_hash_local_spec']
endpoints = [lm + '.elements_' + p + '_annex_hash_literal_local_spec' for p in ['input', 'current']]
if any(deps[a] != deps[b] for a, b in zip(endpoints, originals)):
    raise ValueError('annex endpoint changed original assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^ANNEX_HASH_(TYPE|DEF) (\S+)$', report) != [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete full contract report')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(work), '--coq', str(coq), '--literal', str(literal)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(work), str(coq), str(literal)], 'source-negative')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
roots = ['C.jet_elements_annex_local', 'C.jet_elements_current_gen_jets', lm]
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/checked source drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'prior_preparation_sha256': support.sha(prior_path.read_bytes()), 'base_input_sha256': prior['candidate_input_sha256'],
          'candidate_input_sha256': fingerprint, 'main_inputs': before, 'staged_patch_sha256': index,
          'new_sources': ['C/jet_elements_optional_digest_literal.v'], 'roots': roots, 'fresh_modules': order,
          'results': results, 'definitions': definitions, 'endpoints': endpoints, 'closed_shared_lemmas': pure,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
          'source_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'object_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['check.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n'}
for n in ['assumptions.log', 'contracts.log', 'source.log', 'source-negative.log', 'ast.log', 'kernel.log']:
    changes[HERE / n] = (work / n).read_text()
support.changed(changes)
print('Two annex-hash C endpoints compile and kernel-check; normal registration not claimed', flush=True)
