"""Compile/kernel-check three new endpoints; canonical-source review still pending.

Reuse only immutable, hash-verified objects from the completed annex proof tree.
This checkpoint deliberately does not register coverage or claim admission.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('indexed_literal_support', HERE.parent / 'elements-count/support.py')
s = importlib.util.module_from_spec(spec)
spec.loader.exec_module(s)
work = Path(sys.argv[1]).resolve()
coq = work / 'Coq'
priorpath = HERE.parent / 'elements-annex-hash/PREPARATION.json'
prior = json.loads(priorpath.read_text())
base = Path(prior['candidate'])
module = 'C.jet_elements_indexed_literal'
path = coq / 'C/jet_elements_indexed_literal.v'
if work == base or s.REPO in work.parents or (HERE / 'CHECKED.json').exists():
    raise ValueError('use a distinct unchecked external tree')
subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-annex-hash/review.py')], check=True)
before, index = s.input_map(), s.index_hash()
if s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']:
    raise ValueError('immutable checked base changed')
paths = s.load('indexed_literal_source_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
inherited = paths(base / 'Coq')
if paths(coq) != inherited | {'C/jet_elements_indexed_literal.v'}:
    raise ValueError('unexpected source/registry inventory')
for name in inherited:
    if (coq / name).read_bytes() != (base / 'Coq' / name).read_bytes():
        raise ValueError('inherited input changed: ' + name)
if path.read_bytes() != (HERE / 'source/jet_elements_indexed_literal.v.source').read_bytes():
    raise ValueError('archive differs from checked source')
reused = {}
for m, expected in prior['object_sha256'].items():
    obj = coq / (m.replace('.', '/') + '.vo')
    if obj.is_symlink() or s.sha(obj.read_bytes()) != expected:
        raise ValueError('inherited object differs: ' + m)
    reused[m] = expected
fingerprint = s.inputs.fingerprint(coq, work)
commands = {}


def run(command, name, timeout=180):
    commands[name] = s.run(work, command, name, timeout)


code = s.safe_source(path.read_text(), module)
results = [module + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
definitions = [module + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
if (len(results), len(definitions)) != (8, 5):
    raise ValueError('wrong new declaration inventory')
run(['bash', 'build-jets.sh', '--coqc', '-q', 'C/jet_elements_indexed_literal.v'], 'literal')
assumptions = ['Require ' + module + '.']
contracts = assumptions + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for n in results:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for n in names:
        contracts += ['Goal True. idtac "INDEXED_LITERAL_' + kind + ' ' + n + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
s.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for name in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (name + '.v'))], name)
deps = s.reports.assumptions((work / 'assumptions.log').read_text())
pure = [module + '.elements_indexed_literal_matches', module + '.haskell_encode_outpoint_matches']
endpoints = [module + '.elements_' + n + '_literal_local_spec' for n in ['input_prev_outpoint', 'current_prev_outpoint', 'output_script_hash']]
originals = ['C.jet_elements_indexed_ptr_jets.elements_input_prev_outpoint_local_spec',
             'C.jet_elements_current_input_jets.elements_current_prev_outpoint_local_spec',
             'C.jet_elements_indexed_ptr_jets.elements_output_script_hash_local_spec']
if (set(deps) != set(results) or any(not d <= s.SIX for d in deps.values()) or
        any(deps[n] for n in pure) or
        any(sorted(deps[n]) != prior['dependencies'][old] for n, old in zip(endpoints, originals))):
    raise ValueError('missing/new assumptions or nonclosed conversion lemmas')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^INDEXED_LITERAL_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete whole-type/definition report')
roots = ['C.jet_elements_indexed_ptr_jets', 'C.jet_elements_current_input_jets', module]
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
s.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (s.input_map() != before or s.index_hash() != index or s.inputs.fingerprint(coq, work) != fingerprint or
        s.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('checked inputs/main/staging drift')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'prior_preparation_sha256': s.sha(priorpath.read_bytes()), 'base_input_sha256': prior['candidate_input_sha256'],
          'candidate_input_sha256': fingerprint, 'main_inputs': before, 'staged_patch_sha256': index,
          'new_sources': ['C/jet_elements_indexed_literal.v'], 'fresh_modules': [module],
          'reused_objects_sha256': reused, 'roots': roots, 'results': results, 'definitions': definitions,
          'endpoints': endpoints, 'closed_shared_lemmas': pure, 'dependencies': {n: sorted(d) for n, d in deps.items()},
          'source_sha256': s.sha(path.read_bytes()), 'object_sha256': s.sha(path.with_suffix('.vo').read_bytes()),
          'commands': commands, 'checkpoint_driver_sha256': s.sha(Path(__file__).read_bytes()),
          'canonical_source_review_complete': False, 'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'CHECKED.json': json.dumps(record, indent=2) + '\n'}
for name in ['literal.log', 'assumptions.log', 'contracts.log', 'kernel.log']:
    changes[HERE / name] = (work / name).read_text()
s.changed(changes)
print('Three actual-C getter endpoints compiled and kernel-checked; canonical-source/normal admission still pending', flush=True)
