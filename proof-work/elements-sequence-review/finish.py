"""Seal a new literal-conversion C contract in an external namespace.

The already-built normal candidate is a read-only dependency tree. All source,
compiler/checker outputs and reports for this experiment stay outside it.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sequence_audit_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work, base = map(lambda p: Path(p).resolve(), sys.argv[1:])
source = work / 'jet_elements_sequence_literal.v'
support.safe_source(source.read_text(), str(source))
frozen = json.loads((base / 'REVIEW.json').read_text())
before = support.inputs.fingerprint(base / 'Coq', base)
if before != frozen['candidate_input_sha256']:
    raise ValueError('read-only dependency source drift')
index = support.index_hash()
commands = {}


def run(command, stem, timeout=1800):
    with (work / (stem + '.log')).open('wb') as log:
        result = subprocess.run(command, cwd=base / 'Coq', env=support.ENV, stdout=log,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('sequence check failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


def coqc(file):
    return ['bash', 'build-jets.sh', '--coqc', '-q', '-Q', str(work), 'SequenceReview', str(file)]


run(coqc(source), 'compile', 120)
prefix = 'SequenceReview.jet_elements_sequence_literal.'
results = [prefix + name for name in ['haskell_from_word_acc_matches', 'haskell_from_word_matches',
            'elements_input_sequence_literal_matches',
            'application_jet_local_spec_sep_pointwise', 'elements_input_sequence_literal_local_spec']]
original = 'C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec'
definitions = [prefix + 'elements_input_sequence_literal_spec', prefix + 'haskell_from_word_acc',
               prefix + 'haskell_from_word', 'C.jet_application_sep.application_jet_local_spec_sep']
assumptions = ['Require SequenceReview.jet_elements_sequence_literal.']
contracts = assumptions + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + [original]:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "SEQUENCE_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check ' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n',
                 work / 'contracts.v': '\n'.join(contracts) + '\n'})
run(coqc(work / 'assumptions.v'), 'assumptions', 120)
run(coqc(work / 'contracts.v'), 'contracts', 120)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + [original]) or any(not ds <= support.SIX for ds in deps.values()) or
        deps[results[-1]] != deps[original]):
    raise ValueError('new/unreviewed assumptions')
output = (work / 'contracts.log').read_text()
wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
import re
if '...' in output or re.findall(r'(?m)^SEQUENCE_(TYPE|DEF) (\S+)$', output) != wanted:
    raise ValueError('incomplete contract/definition report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', '-Q', str(work), 'SequenceReview',
     'SequenceReview.jet_elements_sequence_literal'], 'kernel')
support.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
run(['bash', 'C/regenerate-elements-jets.sh', str(work / 'regenerated.v')], 'AST', 120)
if (work / 'regenerated.v').read_bytes() != (base / 'Coq/C/jets_elements.v').read_bytes():
    raise ValueError('original Elements AST mismatch')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO), '--coq', str(base / 'Coq'),
     '--literal', str(source)], 'source', 120)
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(base / 'Coq'), str(source)], 'source-tests', 120)
if support.inputs.fingerprint(base / 'Coq', base) != before or support.index_hash() != index:
    raise ValueError('frozen source or main index drift')
record = {'candidate': str(work), 'dependency_tree': str(base), 'namespace': 'SequenceReview',
          'source_sha256': support.sha(source.read_bytes()), 'dependency_input_sha256': before,
          'staged_patch_sha256': index, 'commands': commands, 'results': results, 'definitions': definitions,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'evidence_sha256': {p.name: support.sha(p.read_bytes()) for p in work.iterdir()
                              if p.is_file() and p.suffix in ['.v', '.vo', '.log']},
          'normal_registration': False, 'coverage_added': 0, 'current_sequence_proved_here': False}
support.changed({HERE / 'source/jet_elements_sequence_literal.v.source': source.read_text(),
                 HERE / 'REVIEW.json': json.dumps(record, indent=2) + '\n',
                 HERE / 'contracts.log': output,
                 HERE / 'assumptions.log': (work / 'assumptions.log').read_text()})
print('Literal InputSequence C contract compiled, fully printed, source-reviewed and recursively kernel-checked; registry unchanged')
