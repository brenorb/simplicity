"""Read-only validation of final-C-name preparation, not normal acceptance."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sealed_sequence_normal_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
record = json.loads((HERE / 'PREPARATION.json').read_text())
work, base = Path(record['candidate']), Path(record['base_candidate'])
coq = work / 'Coq'
if (record['namespace'] != 'C' or record['normal_registration'] is not False or
        record['coverage_added'] != 0 or record['full_acceptance'] is not False or
        support.inputs.fingerprint(base / 'Coq', base) != record['base_input_sha256'] or
        support.inputs.fingerprint(coq, REPO) != record['candidate_input_sha256']):
    raise ValueError('source/preparation scope drift')
modules = record['missing_dependency_modules']
if len(set(modules)) != len(modules) or set(modules) != set(record['sources_sha256']) or set(modules) != set(record['objects_sha256']):
    raise ValueError('incomplete fresh module evidence')
for module in modules:
    source = coq / (module.replace('.', '/') + '.v')
    support.safe_source(source.read_text(), str(source))
    if (support.sha(source.read_bytes()) != record['sources_sha256'][module] or
            support.sha(source.with_suffix('.vo').read_bytes()) != record['objects_sha256'][module]):
        raise ValueError('source/object drift')
sources = ['jet_elements_sequence_literal', 'jet_elements_current_sequence_literal']
for module, previous in zip(sources, ['elements-sequence-review', 'elements-current-sequence']):
    source = coq / 'C' / (module + '.v')
    old = (HERE.parent / previous / 'source' / (module + '.v.source')).read_text()
    if module == sources[1]:
        old = old.replace('Require Import SequenceReview.jet_elements_sequence_literal.',
                          'Require Import C.jet_elements_sequence_literal.')
    if source.read_text() != old or source.read_bytes() != (HERE / 'source' / (module + '.v.source')).read_bytes():
        raise ValueError('namespace change altered a proof')
commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in modules}
commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))]
                 for n in ['contracts', 'assumptions']})
commands.update({'kernel': ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o',
                            'C.jet_elements_sequence_literal', 'C.jet_elements_current_sequence_literal'],
                 'source': [sys.executable, '-B', str(HERE.parent / 'elements-current-sequence/check-source.py'),
                     '--repo', str(REPO), '--coq', str(coq), '--sequence', str(coq / 'C/jet_elements_sequence_literal.v'),
                     '--literal', str(coq / 'C/jet_elements_current_sequence_literal.v')]})
if set(commands) != set(record['commands']):
    raise ValueError('incomplete compiler/checker stages')
for name, command in commands.items():
    row = record['commands'][name]
    if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes())):
        raise ValueError('command/terminal evidence drift')
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if {n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or any(not ds <= support.SIX for ds in deps.values()):
    raise ValueError('unreviewed assumptions')
for literal, original in [('C.jet_elements_sequence_literal.elements_input_sequence_literal_local_spec',
                           'C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec'),
                          ('C.jet_elements_current_sequence_literal.elements_current_sequence_literal_local_spec',
                           'C.jet_elements_current_jets.elements_current_sequence_local_spec')]:
    if deps[literal] != deps[original]:
        raise ValueError('actual-C result assumptions changed')
contracts = (work / 'contracts.log').read_text()
originals = ['C.jet_elements_indexed_scalar_jets.elements_input_sequence_local_spec',
             'C.jet_elements_current_jets.elements_current_sequence_local_spec']
if ('...' in contracts or re.search(r'\?[A-Za-z]', contracts) or
        re.findall(r'(?m)^SEQUENCE_NORMAL_(TYPE|DEF) (\S+)$', contracts) !=
        [('TYPE', n) for n in record['results'] + originals] + [('DEF', n) for n in record['definitions']] or
        (HERE / 'contracts.log').read_text() != contracts or
        (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
    raise ValueError('incomplete/altered full reports')
support.kernel.kernel((work / 'kernel.log').read_text(),
                       sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
guard = support.load('sealed_final_sequence_source', HERE.parent / 'elements-current-sequence/check-source.py')
guard.check(REPO, coq, coq / 'C/jet_elements_sequence_literal.v', coq / 'C/jet_elements_current_sequence_literal.v')
print('Final C namespaces, unchanged proofs, fresh dependency objects and recursive kernel evidence validated; no admission claimed')
