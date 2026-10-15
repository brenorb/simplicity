"""Check the three direct getters under final C names; never install into main."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('direct_getters_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
sequence = json.loads((HERE.parent / 'elements-sequence-admission/ASSEMBLY.json').read_text())
base = Path(sequence['candidate'])
sealed = json.loads((base / 'REVIEW.json').read_text())
if work == base or work == REPO or REPO in work.parents:
    raise ValueError('direct-getter preparation requires its own external directory')
for package in ['elements-tapleaf-literal', 'elements-hash-literal']:
    subprocess.run([sys.executable, '-B', str(HERE.parent / package / 'review.py')], check=True)
if support.inputs.fingerprint(base / 'Coq', base) != sealed['candidate_input_sha256']:
    raise ValueError('reviewed sequence base source drift')
if (work / 'Coq').exists():
    raise ValueError('use a fresh empty preparation directory')
subprocess.run(['cp', '-cR', str(base / 'Coq'), str(work / 'Coq')], check=True)
for name in ['C', 'Haskell']:
    (work / name).symlink_to(REPO / name, target_is_directory=True)
coq = work / 'Coq'
before, index = support.inputs.fingerprint(), support.index_hash()
sources = {'jet_elements_tapleaf_literal': 'elements-tapleaf-literal',
           'jet_haskell_hash_word': 'elements-hash-literal',
           'jet_elements_hash_literal': 'elements-hash-literal'}
changes = {}
for module, package in sources.items():
    text = (HERE.parent / package / 'source' / (module + '.v.source')).read_text()
    if module == 'jet_elements_hash_literal':
        old = 'Require Import HashLiteral.jet_haskell_hash_word.'
        if text.count(old) != 1:
            raise ValueError('unexpected literal digest import')
        text = text.replace(old, 'Require Import C.jet_haskell_hash_word.')
    support.safe_source(text, module)
    changes[coq / 'C' / (module + '.v')] = text
support.changed(changes)
for p in coq.rglob('*'):
    if p.is_file() and p.suffix == '.v' and p.stem not in sources:
        original = base / 'Coq' / p.relative_to(coq)
        if not original.exists() or original.read_bytes() != p.read_bytes():
            raise ValueError('inherited source changed in independent copy')
copied = support.inputs.fingerprint(coq, work)
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())
visited, visiting, order = set(), set(), []


def visit(module):
    if module in visited:
        return
    if module in visiting:
        raise ValueError('cyclic C proof dependency')
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


for module in sources:
    visit('C.' + module)
commands = {}


def run(command, stem, timeout=180):
    with (work / (stem + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=coq, env=support.ENV, stdout=output,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('direct-getter preparation failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


print('Additional normal dependency closure: ' + ', '.join(order), flush=True)
for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
results, definitions, pure = [], [], []
for module in sources:
    code = support.safe_source((coq / 'C' / (module + '.v')).read_text(), module)
    names = ['C.' + module + '.' + n for n in re.findall(r'^(?:Lemma|Theorem)\s+(\w+)', code, re.M)]
    results += names
    if module == 'jet_haskell_hash_word':
        pure = names
    definitions += ['C.' + module + '.' + n for n in re.findall(r'^(?:Definition|Fixpoint|Record)\s+(\w+)', code, re.M)]
originals = ['C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec',
             'C.jet_elements_script_cmr_local.elements_script_cmr_local_spec',
             'C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec']
finals = ['C.jet_elements_tapleaf_literal.elements_tapleaf_version_literal_local_spec',
          'C.jet_elements_hash_literal.elements_script_cmr_literal_local_spec',
          'C.jet_elements_hash_literal.elements_genesis_hash_literal_local_spec']
driver = ['Require C.jet_elements_tapleaf_literal C.jet_elements_hash_literal.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + originals:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results + originals), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "DIRECT_GETTER_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (stem + '.v'))], stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + originals) or any(not ds <= support.SIX for ds in deps.values()) or
        any(deps[n] for n in pure) or any(deps[n] != deps[o] for n, o in zip(finals, originals))):
    raise ValueError('new/unreviewed final-name assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^DIRECT_GETTER_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results + originals] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete final-name contract report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o',
     'C.jet_elements_tapleaf_literal', 'C.jet_elements_hash_literal'], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
for package, flags, positional in [
    ('elements-tapleaf-literal', ['--literal', 'C/jet_elements_tapleaf_literal.v'], ['C/jet_elements_tapleaf_literal.v']),
    ('elements-hash-literal', ['--helper', 'C/jet_haskell_hash_word.v', '--endpoint', 'C/jet_elements_hash_literal.v'],
     ['C/jet_haskell_hash_word.v', 'C/jet_elements_hash_literal.v'])]:
    run([sys.executable, '-B', str(HERE.parent / package / 'check-source.py'), '--repo', str(work), '--coq', '.'] + flags, package + '-source')
    run([sys.executable, '-B', str(HERE.parent / package / 'test-source.py'), str(work), '.'] + positional, package + '-negative')
if (support.inputs.fingerprint() != before or support.index_hash() != index or
        support.inputs.fingerprint(coq, work) != copied or
        support.inputs.fingerprint(base / 'Coq', base) != sealed['candidate_input_sha256']):
    raise ValueError('main/index/independent/base source drift during preparation')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'C',
          'base_input_sha256': sealed['candidate_input_sha256'], 'candidate_input_sha256': copied,
          'main_input_sha256': before, 'staged_patch_sha256': index, 'modules': list(sources),
          'missing_dependency_modules': order, 'results': results, 'pure_results': pure,
          'definitions': definitions, 'originals': originals, 'finals': finals, 'commands': commands,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'sources_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'objects_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
archives = {HERE / 'PREPARATION.json': json.dumps(record, indent=2) + '\n',
            HERE / 'contracts.log': report, HERE / 'assumptions.log': (work / 'assumptions.log').read_text()}
archives.update({HERE / 'source' / (m + '.v.source'): (coq / 'C' / (m + '.v')).read_text() for m in sources})
support.changed(archives)
print('Three direct-getter C contracts pass final-name source/kernel checks; registration and full admission remain pending')
