"""Read-only validation of the sealed literal InputSequence evidence."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sequence_sealed_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)


def review():
    record = json.loads((HERE / 'REVIEW.json').read_text())
    work, base = Path(record['candidate']), Path(record['dependency_tree'])
    prefix = 'SequenceReview.jet_elements_sequence_literal.'
    names = ['haskell_from_word_acc_matches', 'haskell_from_word_matches',
             'elements_input_sequence_literal_matches', 'application_jet_local_spec_sep_pointwise',
             'elements_input_sequence_literal_local_spec']
    results = [prefix + n for n in names]
    definitions = [prefix + n for n in ['elements_input_sequence_literal_spec', 'haskell_from_word_acc', 'haskell_from_word']]
    definitions += ['C.jet_application_sep.application_jet_local_spec_sep']
    original = 'C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec'
    if (record['namespace'] != 'SequenceReview' or record['results'] != results or
            record['definitions'] != definitions or record['normal_registration'] is not False or
            record['coverage_added'] != 0 or record['current_sequence_proved_here'] is not False):
        raise ValueError('wrong literal sequence scope')
    source = work / 'jet_elements_sequence_literal.v'
    archived = HERE / 'source/jet_elements_sequence_literal.v.source'
    if source.read_bytes() != archived.read_bytes() or support.sha(source.read_bytes()) != record['source_sha256']:
        raise ValueError('literal source/archive drift')
    support.safe_source(source.read_text(), str(source))
    for name, digest in record['evidence_sha256'].items():
        path = work / name
        if path.parent != work or path.is_symlink() or support.sha(path.read_bytes()) != digest:
            raise ValueError('compiled/report/terminal evidence drift')
    if record['dependency_input_sha256'] != support.inputs.fingerprint(base / 'Coq', base):
        raise ValueError('read-only dependency source drift')
    def coqc(path):
        return ['bash', 'build-jets.sh', '--coqc', '-q', '-Q', str(work), 'SequenceReview', str(path)]
    commands = {
        'compile': coqc(source), 'assumptions': coqc(work / 'assumptions.v'), 'contracts': coqc(work / 'contracts.v'),
        'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', '-Q', str(work), 'SequenceReview',
                   'SequenceReview.jet_elements_sequence_literal'],
        'AST': ['bash', 'C/regenerate-elements-jets.sh', str(work / 'regenerated.v')],
        'source': [sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO),
                   '--coq', str(base / 'Coq'), '--literal', str(source)],
        'source-tests': [sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(base / 'Coq'), str(source)],
    }
    if set(record['commands']) != set(commands):
        raise ValueError('missing verification phase')
    for name, command in commands.items():
        row = record['commands'][name]
        if (row['command'] != command or row['exit_code'] != 0 or
                row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
            raise ValueError('command/exit/terminal evidence drift')
    deps = support.reports.assumptions((work / 'assumptions.log').read_text())
    if ({n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
            set(deps) != set(results + [original]) or any(not ds <= support.SIX for ds in deps.values()) or
            any(deps[prefix + n] for n in names[:2]) or deps[results[-1]] != deps[original]):
        raise ValueError('new or unreviewed assumptions')
    text = (work / 'contracts.log').read_text()
    if ('...' in text or re.findall(r'(?m)^SEQUENCE_(TYPE|DEF) (\S+)$', text) !=
            [('TYPE', n) for n in results] + [('DEF', n) for n in definitions] or
            (HERE / 'contracts.log').read_text() != text or
            (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
        raise ValueError('incomplete/changed full reports')
    support.kernel.kernel((work / 'kernel.log').read_text(),
                           sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
    if (work / 'regenerated.v').read_bytes() != (base / 'Coq/C/jets_elements.v').read_bytes():
        raise ValueError('wrong original C program')
    source_guard = support.load('sealed_sequence_source', HERE / 'check-source.py')
    source_guard.check(REPO, base / 'Coq', source)
    print('Five sequence results, full C contract, literal input/output conversions and recursive kernel evidence validated')


if __name__ == '__main__':
    review()
