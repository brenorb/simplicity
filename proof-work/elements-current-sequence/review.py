"""Read-only check of the sealed actual-C CurrentSequence proof evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sealed_current_sequence_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review(record=None):
    if record is None:
        record = json.loads((HERE / 'REVIEW.json').read_text())
    work, base, sequence = map(Path, [record['candidate'], record['base_candidate'], record['sequence_candidate']])
    proof = work / 'Proof'
    source = proof / 'jet_elements_current_sequence_literal.v'
    prefix = 'CurrentSequenceReview.jet_elements_current_sequence_literal.'
    results = [prefix + name for name in ['elements_current_literal_sem',
               'elements_current_sequence_literal_matches', 'elements_current_sequence_literal_local_spec']]
    original = 'C.jet_elements_current_jets.elements_current_sequence_local_spec'
    definitions = [prefix + name for name in ['elements_current_literal_result', 'elements_current_sequence_literal_spec']]
    definitions += ['C.jet_application_contract.application_jet_local_spec',
                    'C.jet_elements_current_jets.current_scalar_rep',
                    'C.jet_elements_current_spec.elements_current_spec',
                    'C.jet_elements_current_spec.elements_assert_spec']
    if (record['namespace'] != 'CurrentSequenceReview' or record['results'] != results or
            record['definitions'] != definitions or record['original'] != original or
            record['normal_registration'] is not False or record['coverage_added'] != 0):
        raise ValueError('wrong proof scope or unearned coverage')
    archived = HERE / 'source/jet_elements_current_sequence_literal.v.source'
    if source.read_bytes() != archived.read_bytes() or support.sha(source.read_bytes()) != record['source_sha256']:
        raise ValueError('literal proof source/archive drift')
    support.safe_source(source.read_text(), str(source))
    for name, digest in record['tools_sha256'].items():
        if support.sha((HERE / name).read_bytes()) != digest:
            raise ValueError('checked driver/source gate drift')
    if set(record['tools_sha256']) != {'finish.py', 'check-source.py', 'test-source.py'}:
        raise ValueError('missing verification tool binding')
    for name, digest in record['evidence_sha256'].items():
        path = work / name
        if (path.parent not in [work, proof] or path.is_symlink() or
                support.sha(path.read_bytes()) != digest):
            raise ValueError('terminal evidence drift')
    required_evidence = {'Proof/jet_elements_current_sequence_literal.v',
                         'Proof/jet_elements_current_sequence_literal.vo',
                         'Proof/contracts.v', 'Proof/assumptions.v',
                         'compile.log', 'contracts.log', 'assumptions.log', 'kernel.log',
                         'AST.log', 'regenerated.v', 'source.log', 'source-tests.log'}
    if not required_evidence <= set(record['evidence_sha256']):
        raise ValueError('missing source/object/terminal evidence')
    if (support.inputs.fingerprint(base / 'Coq', base) != record['base_input_sha256'] or
            support.inputs.fingerprint(work / 'Coq', REPO) != record['coq_input_sha256']):
        raise ValueError('checked dependency source drift')
    sequence_review = support.load('sealed_current_input_review', HERE.parent / 'elements-sequence-review/review.py')
    sequence_review.review()
    if str(sequence) != json.loads((HERE.parent / 'elements-sequence-review/REVIEW.json').read_text())['candidate']:
        raise ValueError('wrong literal input dependency')
    flags = ['-Q', str(sequence), 'SequenceReview', '-Q', str(proof), 'CurrentSequenceReview']
    def coqc(file):
        return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(file)]
    commands = {name: coqc(Path('C') / (name + '.v')) for name in
                ['jet_elements_current_spec', 'jet_elements_current_exec', 'jet_elements_current_jets']}
    commands.update({'compile': coqc(source), 'assumptions': coqc(proof / 'assumptions.v'),
                     'contracts': coqc(proof / 'contracts.v'),
                     'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags +
                         ['CurrentSequenceReview.jet_elements_current_sequence_literal'],
                     'AST': ['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')],
                     'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO),
                         '--coq', str(work / 'Coq'), '--sequence', str(sequence / 'jet_elements_sequence_literal.v'),
                         '--literal', str(source)],
                     'source-tests': [sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(work / 'Coq'),
                         str(sequence / 'jet_elements_sequence_literal.v'), str(source)]})
    if set(record['commands']) != set(commands):
        raise ValueError('missing verification stage')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('command/exit/log mismatch')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if ({n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
            set(deps) != set(results + [original]) or any(not ds <= support.SIX for ds in deps.values()) or
            deps[results[-1]] != deps[original]):
        raise ValueError('new/unreviewed assumptions')
    contracts = (work / 'contracts.log').read_text()
    if ('...' in contracts or re.search(r'\?[A-Za-z]', contracts) or
            re.findall(r'(?m)^CURRENT_SEQUENCE_(TYPE|DEF) (\S+)$', contracts) !=
            [('TYPE', n) for n in results + [original]] + [('DEF', n) for n in definitions] or
            (HERE / 'contracts.log').read_text() != contracts or
            (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
        raise ValueError('incomplete/changed full reports')
    support.kernel.kernel((work / 'kernel.log').read_text(),
                           sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    if (work / 'regenerated.v').read_bytes() != (work / 'Coq/C/jets_elements.v').read_bytes():
        raise ValueError('production AST differs')
    guard = support.load('sealed_current_sequence_source', HERE / 'check-source.py')
    guard.check(REPO, work / 'Coq', sequence / 'jet_elements_sequence_literal.v', source)
    print('Three CurrentSequence results, full actual-C contract, source correspondence and recursive kernel evidence validated')


if __name__ == '__main__':
    review()
