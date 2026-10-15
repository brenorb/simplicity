"""Compile and seal an isolated actual-C CurrentSequence contract.

The dependency tree is an independent copy of the frozen normal candidate.
Nothing is installed into the running count audit or the normal registry.
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
spec = importlib.util.spec_from_file_location('current_sequence_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work, base, sequence = map(lambda p: Path(p).resolve(), sys.argv[1:])
proof = work / 'Proof'
source = proof / 'jet_elements_current_sequence_literal.v'
support.safe_source(source.read_text(), str(source))
before = support.inputs.fingerprint(base / 'Coq', base)
if before != json.loads((base / 'REVIEW.json').read_text())['candidate_input_sha256']:
    raise ValueError('frozen normal candidate drift')
for p in (work / 'Coq').rglob('*'):
    if p.is_file() and p.suffix == '.v':
        original = base / 'Coq' / p.relative_to(work / 'Coq')
        if not original.is_file() or p.read_bytes() != original.read_bytes():
            raise ValueError('independent Coq source differs: ' + str(p))
input_receipt = json.loads((HERE.parent / 'elements-sequence-review/REVIEW.json').read_text())
if (str(sequence) != input_receipt['candidate'] or
        support.sha((sequence / 'jet_elements_sequence_literal.v').read_bytes()) != input_receipt['source_sha256']):
    raise ValueError('literal input dependency drift')
for name, digest in input_receipt['evidence_sha256'].items():
    if support.sha((sequence / name).read_bytes()) != digest:
        raise ValueError('literal input compiled evidence drift')
index = support.index_hash()
main_before = support.inputs.fingerprint()
coq_before = support.inputs.fingerprint(work / 'Coq', REPO)
commands = {}
flags = ['-Q', str(sequence), 'SequenceReview', '-Q', str(proof), 'CurrentSequenceReview']


def run(command, stem, timeout=120):
    with (work / (stem + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=work / 'Coq', env=support.ENV,
                                stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('CurrentSequence verification failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


def coqc(file):
    return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(file)]


for name in ['jet_elements_current_spec', 'jet_elements_current_exec', 'jet_elements_current_jets']:
    run(coqc(Path('C') / (name + '.v')), name, 180)
run(coqc(source), 'compile')
prefix = 'CurrentSequenceReview.jet_elements_current_sequence_literal.'
results = [prefix + name for name in ['elements_current_literal_sem',
           'elements_current_sequence_literal_matches', 'elements_current_sequence_literal_local_spec']]
original = 'C.jet_elements_current_jets.elements_current_sequence_local_spec'
definitions = [prefix + name for name in ['elements_current_literal_result', 'elements_current_sequence_literal_spec']]
definitions += ['C.jet_application_contract.application_jet_local_spec',
                'C.jet_elements_current_jets.current_scalar_rep',
                'C.jet_elements_current_spec.elements_current_spec',
                'C.jet_elements_current_spec.elements_assert_spec']
assumptions = ['Require CurrentSequenceReview.jet_elements_current_sequence_literal.']
contracts = assumptions + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + [original]:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results + [original]), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "CURRENT_SEQUENCE_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({proof / 'assumptions.v': '\n'.join(assumptions) + '\n',
                 proof / 'contracts.v': '\n'.join(contracts) + '\n'})
run(coqc(proof / 'assumptions.v'), 'assumptions')
run(coqc(proof / 'contracts.v'), 'contracts')
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + [original]) or any(not ds <= support.SIX for ds in deps.values()) or
        deps[results[-1]] != deps[original]):
    raise ValueError('new assumptions or changed C-contract dependencies')
output = (work / 'contracts.log').read_text()
wanted = [('TYPE', n) for n in results + [original]] + [('DEF', n) for n in definitions]
if ('...' in output or re.search(r'\?[A-Za-z]', output) or
        re.findall(r'(?m)^CURRENT_SEQUENCE_(TYPE|DEF) (\S+)$', output) != wanted):
    raise ValueError('incomplete full contract/definition report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags +
    ['CurrentSequenceReview.jet_elements_current_sequence_literal'], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
run(['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')], 'AST')
if (work / 'regenerated.v').read_bytes() != (work / 'Coq/C/jets_elements.v').read_bytes():
    raise ValueError('original C AST differs')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO), '--coq', str(work / 'Coq'),
     '--sequence', str(sequence / 'jet_elements_sequence_literal.v'), '--literal', str(source)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(work / 'Coq'),
     str(sequence / 'jet_elements_sequence_literal.v'), str(source)], 'source-tests')
if (support.inputs.fingerprint(base / 'Coq', base) != before or support.index_hash() != index or
        support.inputs.fingerprint() != main_before or
        support.inputs.fingerprint(work / 'Coq', REPO) != coq_before):
    raise ValueError('source/index drift during verification')
record = {'candidate': str(work), 'base_candidate': str(base), 'sequence_candidate': str(sequence),
          'namespace': 'CurrentSequenceReview', 'source_sha256': support.sha(source.read_bytes()),
          'base_input_sha256': before, 'coq_input_sha256': coq_before, 'main_input_sha256': main_before,
          'staged_patch_sha256': index, 'commands': commands, 'results': results,
          'definitions': definitions, 'original': original,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes())
              for directory in [work, proof] for p in directory.iterdir()
              if p.is_file() and p.suffix in ['.v', '.vo', '.log']},
          'tools_sha256': {name: support.sha((HERE / name).read_bytes())
                           for name in ['finish.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0}
support.changed({HERE / 'source/jet_elements_current_sequence_literal.v.source': source.read_text(),
                 HERE / 'REVIEW.json': json.dumps(record, indent=2) + '\n',
                 HERE / 'contracts.log': output,
                 HERE / 'assumptions.log': (work / 'assumptions.log').read_text()})
print('CurrentSequence actual-C literal contract and reusable assertion bridge passed all isolated checks; no normal coverage added')
