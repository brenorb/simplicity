"""Check the two sequence modules under final C names, without registering.

This is preparation for a later normal admission, not whole-registry acceptance.
Use an independent clone of the immutable accepted count candidate; never copy
live main compiler outputs or write to main during its acceptance run.
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
spec = importlib.util.spec_from_file_location('sequence_normal_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
count = json.loads((HERE.parent / 'elements-count-admission/INSTALLATION.json').read_text())
base = Path(count['candidate'])
if support.inputs.fingerprint(base / 'Coq', base) != count['candidate_input_sha256']:
    raise ValueError('accepted count source drift')
support.load('sequence_normal_prior_review', HERE.parent / 'elements-current-sequence/review.py').review()
if not (work / 'Coq').exists():
    subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
coq = work / 'Coq'
# Verify this is the intended independent snapshot, not the live checkout.
if work == REPO or REPO in work.parents or coq.is_symlink():
    raise ValueError('normal preparation must be outside the repository')
before, index = support.inputs.fingerprint(), support.index_hash()
source_archives = {
    'jet_elements_sequence_literal': HERE.parent / 'elements-sequence-review/source/jet_elements_sequence_literal.v.source',
    'jet_elements_current_sequence_literal': HERE.parent / 'elements-current-sequence/source/jet_elements_current_sequence_literal.v.source',
}
changes = {}
for module, archive in source_archives.items():
    text = archive.read_text()
    if module == 'jet_elements_current_sequence_literal':
        old = 'Require Import SequenceReview.jet_elements_sequence_literal.'
        if text.count(old) != 1:
            raise ValueError('unexpected namespace dependency')
        text = text.replace(old, 'Require Import C.jet_elements_sequence_literal.')
    support.safe_source(text, module)
    changes[coq / 'C' / (module + '.v')] = text
support.changed(changes)
for path in coq.rglob('*'):
    if path.is_file() and path.suffix == '.v' and path.stem not in source_archives:
        original = base / 'Coq' / path.relative_to(coq)
        if not original.is_file() or original.read_bytes() != path.read_bytes():
            raise ValueError('unexpected dependency source change: ' + str(path))

manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
order, visiting, visited = [], set(), set()


def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise ValueError('cyclic local dependency: ' + module)
    visiting.add(module)
    path = coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(path.read_text(), str(path))
    for declaration in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in declaration.split():
            if dependency.startswith('C.'):
                visit(dependency)
    visiting.remove(module)
    visited.add(module)
    if module.replace('.', '/') + '.v' not in manifest:
        order.append(module)


for module in source_archives:
    visit('C.' + module)
commands = {}


def run(command, stem, timeout=180):
    with (work / (stem + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=coq, env=support.ENV, stdout=output,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('normal sequence preparation failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


print('Final-name dependency additions: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module, 180)
results = []
definitions = []
for module in source_archives:
    code = support.safe_source((coq / 'C' / (module + '.v')).read_text(), module)
    results += ['C.' + module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
    definitions += ['C.' + module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint)\s+(\w+)', code, re.M)]
if len(results) != 8 or len(definitions) != 5:
    raise ValueError('unexpected final-name literal result/definition inventory')
originals = ['C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec',
             'C.jet_elements_current_jets.elements_current_sequence_local_spec']
driver = ['Require C.jet_elements_sequence_literal C.jet_elements_current_sequence_literal.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + originals:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results + originals), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "SEQUENCE_NORMAL_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n',
                 work / 'contracts.v': '\n'.join(contracts) + '\n'})
for name in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (name + '.v'))], name)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + originals) or any(not ds <= support.SIX for ds in deps.values()) or
        deps['C.jet_elements_sequence_literal.elements_input_sequence_literal_local_spec'] != deps[originals[0]] or
        deps['C.jet_elements_current_sequence_literal.elements_current_sequence_literal_local_spec'] != deps[originals[1]]):
    raise ValueError('final-name assumptions changed')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^SEQUENCE_NORMAL_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results + originals] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete final-name contract report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o',
     'C.jet_elements_sequence_literal', 'C.jet_elements_current_sequence_literal'], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
run([sys.executable, '-B', str(HERE.parent / 'elements-current-sequence/check-source.py'),
     '--repo', str(REPO), '--coq', str(coq), '--sequence', str(coq / 'C/jet_elements_sequence_literal.v'),
     '--literal', str(coq / 'C/jet_elements_current_sequence_literal.v')], 'source')
if support.inputs.fingerprint() != before or support.index_hash() != index:
    raise ValueError('main inputs/staging changed during preparation')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'base_input_sha256': count['candidate_input_sha256'],
          'candidate_input_sha256': support.inputs.fingerprint(coq, REPO),
          'main_input_sha256': before, 'staged_patch_sha256': index,
          'missing_dependency_modules': order, 'results': results, 'definitions': definitions,
          'commands': commands, 'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'sources_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'objects_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
archives = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n',
            HERE / 'contracts.log': report, HERE / 'assumptions.log': (work / 'assumptions.log').read_text()}
archives.update({HERE / 'source' / (m + '.v.source'): (coq / 'C' / (m + '.v')).read_text() for m in source_archives})
support.changed(archives)
print('Both actual-C sequence contracts compile and pass recursive kernel checking under final C names; registry unchanged', flush=True)
