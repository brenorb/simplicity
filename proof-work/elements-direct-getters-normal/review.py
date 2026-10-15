"""Validate final-C-name direct-getter preparation, not normal admission."""
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('sealed_direct_getters_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
record = json.loads((HERE / 'PREPARATION.json').read_text())
work, base = Path(record['candidate']), Path(record['base_candidate'])
coq = work / 'Coq'
modules = ['jet_elements_tapleaf_literal', 'jet_haskell_hash_word', 'jet_elements_hash_literal']
originals = ['C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec',
             'C.jet_elements_script_cmr_local.elements_script_cmr_local_spec',
             'C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec']
finals = ['C.jet_elements_tapleaf_literal.elements_tapleaf_version_literal_local_spec',
          'C.jet_elements_hash_literal.elements_script_cmr_literal_local_spec',
          'C.jet_elements_hash_literal.elements_genesis_hash_literal_local_spec']
if (record['namespace'] != 'C' or record['modules'] != modules or record['originals'] != originals or record['finals'] != finals or
        record['normal_registration'] is not False or record['coverage_added'] != 0 or record['full_acceptance'] is not False):
    raise ValueError('wrong direct-getter preparation scope')
if (support.inputs.fingerprint(coq, work) != record['candidate_input_sha256'] or
        support.inputs.fingerprint(base / 'Coq', base) != record['base_input_sha256']):
    raise ValueError('prepared/base source drift')
results, definitions, pure = [], [], []
for module, package in zip(modules, ['elements-tapleaf-literal', 'elements-hash-literal', 'elements-hash-literal']):
    source = coq / 'C' / (module + '.v')
    old = (HERE.parent / package / 'source' / (module + '.v.source')).read_text()
    if module == modules[-1]:
        old = old.replace('Require Import HashLiteral.jet_haskell_hash_word.', 'Require Import C.jet_haskell_hash_word.')
    if source.read_text() != old or source.read_bytes() != (HERE / 'source' / (module + '.v.source')).read_bytes():
        raise ValueError('namespace rebasing altered a proof')
    code = support.safe_source(source.read_text(), str(source))
    names = ['C.' + module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
    results += names
    if module == modules[1]:
        pure = names
    definitions += ['C.' + module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
if record['results'] != results or record['pure_results'] != pure or record['definitions'] != definitions:
    raise ValueError('incomplete result/definition inventory')
order = record['missing_dependency_modules']
if len(set(order)) != len(order) or set(order) != set(record['sources_sha256']) or set(order) != set(record['objects_sha256']):
    raise ValueError('incomplete fresh dependency inventory')
for module in order:
    path = coq / (module.replace('.', '/') + '.v')
    support.safe_source(path.read_text(), str(path))
    if support.sha(path.read_bytes()) != record['sources_sha256'][module] or support.sha(path.with_suffix('.vo').read_bytes()) != record['objects_sha256'][module]:
        raise ValueError('fresh dependency source/object drift')
commands = {m: ['bash', 'build-jets.sh', '--coqc', '-q', m.replace('.', '/') + '.v'] for m in order}
commands.update({n: ['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))] for n in ['assumptions', 'contracts']})
commands['kernel'] = ['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', 'C.jet_elements_tapleaf_literal', 'C.jet_elements_hash_literal']
for package, flags, positional in [
    ('elements-tapleaf-literal', ['--literal', 'C/jet_elements_tapleaf_literal.v'], ['C/jet_elements_tapleaf_literal.v']),
    ('elements-hash-literal', ['--helper', 'C/jet_haskell_hash_word.v', '--endpoint', 'C/jet_elements_hash_literal.v'],
     ['C/jet_haskell_hash_word.v', 'C/jet_elements_hash_literal.v'])]:
    commands[package + '-source'] = [sys.executable, '-B', str(HERE.parent / package / 'check-source.py'), '--repo', str(work), '--coq', '.'] + flags
    commands[package + '-negative'] = [sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.'] + positional
if set(commands) != set(record['commands']):
    raise ValueError('missing final-name compiler/checker stage')
for name, command in commands.items():
    row = record['commands'][name]
    if row['command'] != command or row['exit_code'] != 0 or row['log_sha256'] != support.sha((work / (name + '.log')).read_bytes()):
        raise ValueError('command/exit/log evidence mismatch')
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + originals) or {n: sorted(ds) for n, ds in deps.items()} != record['dependencies'] or
        any(not ds <= support.SIX for ds in deps.values()) or any(deps[n] for n in pure) or
        any(deps[n] != deps[o] for n, o in zip(finals, originals))):
    raise ValueError('unreviewed assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^DIRECT_GETTER_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results + originals] + [('DEF', n) for n in definitions] or
        (HERE / 'contracts.log').read_text() != report or
        (HERE / 'assumptions.log').read_text() != (work / 'assumptions.log').read_text()):
    raise ValueError('incomplete/changed full reports')
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
print('Three final-C-name getters, 27 closed shared lemmas, fresh dependencies and recursive kernel evidence validated; no admission claimed')
