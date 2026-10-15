"""Seal the shared literal digest bridge and two complete original-C contracts."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('hash_literal_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
coq, proof = work / 'Coq', work / 'Proof'
modules = ['jet_haskell_hash_word', 'jet_elements_hash_literal']
old_modules = ['jet_elements_script_cmr_local', 'jet_elements_genesis_hash_local']
prior = json.loads((HERE.parent / 'elements-tapleaf-literal/REVIEW.json').read_text())
base = Path(prior['candidate'])
support.load('hash_literal_tapleaf_base', HERE.parent / 'elements-tapleaf-literal/review.py').review()
if support.inputs.fingerprint(coq, REPO) != prior['coq_input_sha256']:
    raise ValueError('copied Coq source drift')
for m, digest in prior['fresh_object_sha256'].items():
    path = coq / (m.replace('.', '/') + '.v')
    if support.sha(path.read_bytes()) != prior['fresh_source_sha256'][m] or support.sha(path.with_suffix('.vo').read_bytes()) != digest:
        raise ValueError('fresh inherited dependency drift')
before, index = support.inputs.fingerprint(), support.index_hash()
copied = support.inputs.fingerprint(coq, REPO)
commands = {}
flags = ['-Q', str(proof), 'HashLiteral']


def run(command, stem, timeout=180):
    with (work / (stem + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=coq, env=support.ENV, stdout=output,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('hash literal check failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


def coqc(path):
    return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(path)]


for module in old_modules:
    run(coqc(Path('C') / (module + '.v')), module)
results, definitions, pure = [], [], []
for module in modules:
    path = proof / (module + '.v')
    code = support.safe_source(path.read_text(), str(path))
    run(coqc(path), module)
    names = ['HashLiteral.' + module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
    results += names
    if module == modules[0]:
        pure = names
    definitions += ['HashLiteral.' + module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
originals = ['C.jet_elements_script_cmr_local.elements_script_cmr_local_spec',
             'C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec']
definitions += ['C.jet_elements_script_cmr_local.elements_script_cmr_env_rep',
                'C.jet_elements_genesis_hash_local.elements_genesis_hash_env_rep',
                'C.jet_elements_script_cmr_local.elements_script_cmr_spec',
                'C.jet_elements_genesis_hash_local.elements_genesis_hash_spec',
                'C.jet_application_sep.application_jet_local_spec_sep']
driver = ['Require HashLiteral.jet_elements_hash_literal.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + originals:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results + originals), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "HASH_LITERAL_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({proof / 'assumptions.v': '\n'.join(assumptions) + '\n', proof / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(coqc(proof / (stem + '.v')), stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + originals) or any(not ds <= support.SIX for ds in deps.values()) or
        any(deps[n] for n in pure)):
    raise ValueError('unexpected assumptions; shared digest lemmas must be closed')
for theorem, original in zip(results[-2:], originals):
    if deps[theorem] != deps[original]:
        raise ValueError('final C contract assumptions changed')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^HASH_LITERAL_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results + originals] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete full hash contract report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags +
    ['HashLiteral.jet_elements_hash_literal'], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
run(['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')], 'AST')
if (work / 'regenerated.v').read_bytes() != (coq / 'C/jets_elements.v').read_bytes():
    raise ValueError('production Elements AST drift')
source_flags = ['--repo', str(REPO), '--coq', str(coq), '--helper', str(proof / (modules[0] + '.v')),
                '--endpoint', str(proof / (modules[1] + '.v'))]
run([sys.executable, '-B', str(HERE / 'check-source.py')] + source_flags, 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(coq),
     str(proof / (modules[0] + '.v')), str(proof / (modules[1] + '.v'))], 'source-tests')
if (support.inputs.fingerprint() != before or support.index_hash() != index or
        support.inputs.fingerprint(coq, REPO) != copied):
    raise ValueError('source/index drift during hash verification')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'HashLiteral',
          'main_input_sha256': before, 'staged_patch_sha256': index, 'coq_input_sha256': copied,
          'modules': modules, 'original_modules': old_modules, 'results': results, 'definitions': definitions,
          'pure_results': pure, 'originals': originals, 'commands': commands,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'source_sha256': {m: support.sha((proof / (m + '.v')).read_bytes()) for m in modules},
          'original_source_sha256': {m: support.sha((coq / 'C' / (m + '.v')).read_bytes()) for m in old_modules},
          'original_object_sha256': {m: support.sha((coq / 'C' / (m + '.vo')).read_bytes()) for m in old_modules},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['finish.py', 'check-source.py', 'test-source.py']},
          'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes()) for directory in [work, proof]
                             for p in directory.iterdir() if p.is_file() and p.suffix in ['.v', '.vo', '.log']},
          'normal_registration': False, 'coverage_added': 0}
archives = {HERE / 'REVIEW.json': json.dumps(record, indent=2) + '\n',
            HERE / 'contracts.log': report, HERE / 'assumptions.log': (work / 'assumptions.log').read_text()}
archives.update({HERE / 'source' / (m + '.v.source'): (proof / (m + '.v')).read_text() for m in modules})
support.changed(archives)
print('Literal four-limb digest bridge and both full actual-C hash getter contracts passed isolated verification; no registration added')
