"""Check the actual-C byte getter with source-identical fresh dependencies."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('tapleaf_audit_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
coq, proof = work / 'Coq', work / 'Proof'
source = proof / 'jet_elements_tapleaf_literal.v'
support.safe_source(source.read_text(), str(source))
prior = json.loads((HERE.parent / 'elements-sequence-normal/PREPARATION.json').read_text())
base = Path(prior['candidate'])
if support.inputs.fingerprint(base / 'Coq', REPO) != prior['candidate_input_sha256']:
    raise ValueError('sealed dependency source drift')
for p in coq.rglob('*'):
    if p.is_file() and p.suffix == '.v' and p.read_bytes() != (base / 'Coq' / p.relative_to(coq)).read_bytes():
        raise ValueError('tapleaf experiment changed an inherited proof source')
for module, digest in prior['objects_sha256'].items():
    path = coq / (module.replace('.', '/') + '.v')
    if (support.sha(path.read_bytes()) != prior['sources_sha256'][module] or
            support.sha(path.with_suffix('.vo').read_bytes()) != digest):
        raise ValueError('sealed sequence dependency source/object drift')
before, index = support.inputs.fingerprint(), support.index_hash()
copied_before = support.inputs.fingerprint(coq, REPO)
commands, visited, order = {}, set(), []
manifest = set((coq / '_CoqProject.jets').read_text().splitlines())


def visit(module):
    if module in visited:
        return
    visited.add(module)
    path = coq / (module.replace('.', '/') + '.v')
    code = support.safe_source(path.read_text(), str(path))
    for declaration in re.findall(r'\bRequire(?:\s+(?:Import|Export))?\s+(.*?)\.(?=\s|$)', code, re.S):
        for dependency in declaration.split():
            if dependency.startswith('C.'):
                visit(dependency)
    if module.replace('.', '/') + '.v' not in manifest and module not in prior['objects_sha256']:
        order.append(module)


visit('C.jet_elements_tapleaf_version_local')


def run(command, stem, timeout=180):
    with (work / (stem + '.log')).open('wb') as output:
        result = subprocess.run(command, cwd=coq, env=support.ENV, stdout=output,
                                stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise ValueError('tapleaf check failed: ' + stem)
    commands[stem] = {'command': command, 'exit_code': result.returncode,
                      'log_sha256': support.sha((work / (stem + '.log')).read_bytes())}


for module in order:
    run(['bash', 'build-jets.sh', '--coqc', '-q', module.replace('.', '/') + '.v'], module)
flags = ['-Q', str(proof), 'TapleafReview']
def coqc(path):
    return ['bash', 'build-jets.sh', '--coqc', '-q'] + flags + [str(path)]
run(coqc(source), 'compile')
prefix = 'TapleafReview.jet_elements_tapleaf_literal.'
results = [prefix + name for name in ['elements_tapleaf_version_literal_matches', 'elements_tapleaf_version_literal_local_spec']]
original = 'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec'
definitions = [prefix + 'elements_tapleaf_version_literal_spec',
               'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_spec',
               'C.jet_elements_tapleaf_version_local.elements_tapleaf_version_env_rep',
               'C.jet_application_sep.application_jet_local_spec_sep']
driver = ['Require TapleafReview.jet_elements_tapleaf_literal.']
assumptions = driver[:]
contracts = driver + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for name in results + [original]:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + name + '". exact I. Qed.', 'Print Assumptions ' + name + '.']
for kind, names in [('TYPE', results + [original]), ('DEF', definitions)]:
    for name in names:
        contracts += ['Goal True. idtac "TAPLEAF_' + kind + ' ' + name + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + name + '.']
support.changed({proof / 'assumptions.v': '\n'.join(assumptions) + '\n',
                 proof / 'contracts.v': '\n'.join(contracts) + '\n'})
for stem in ['assumptions', 'contracts']:
    run(coqc(proof / (stem + '.v')), stem)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
if (set(deps) != set(results + [original]) or any(not ds <= support.SIX for ds in deps.values()) or
        deps[results[-1]] != deps[original]):
    raise ValueError('new/unreviewed tapleaf assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or
        re.findall(r'(?m)^TAPLEAF_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results + [original]] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete tapleaf type/definition report')
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o'] + flags +
    ['TapleafReview.jet_elements_tapleaf_literal'], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((base / 'Coq/C/jet_coqchk_axioms.expected').read_text().split()))
run(['bash', str(REPO / 'Coq/C/regenerate-elements-jets.sh'), str(work / 'regenerated.v')], 'AST')
if (work / 'regenerated.v').read_bytes() != (coq / 'C/jets_elements.v').read_bytes():
    raise ValueError('tapleaf original C AST drift')
run([sys.executable, '-B', str(HERE / 'check-source.py'), '--repo', str(REPO), '--coq', str(coq),
     '--literal', str(source)], 'source')
run([sys.executable, '-B', str(HERE / 'test-source.py'), str(REPO), str(coq), str(source)], 'source-tests')
if (support.inputs.fingerprint() != before or support.index_hash() != index or
        support.inputs.fingerprint(coq, REPO) != copied_before):
    raise ValueError('main/index/independent source drift during tapleaf checking')
record = {'candidate': str(work), 'base_candidate': str(base), 'namespace': 'TapleafReview',
          'main_input_sha256': before, 'staged_patch_sha256': index, 'coq_input_sha256': copied_before,
          'source_sha256': support.sha(source.read_bytes()), 'results': results, 'definitions': definitions,
          'original': original, 'fresh_modules': order, 'commands': commands,
          'dependencies': {n: sorted(ds) for n, ds in deps.items()},
          'fresh_source_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.v')).read_bytes()) for m in order},
          'fresh_object_sha256': {m: support.sha((coq / (m.replace('.', '/') + '.vo')).read_bytes()) for m in order},
          'evidence_sha256': {str(p.relative_to(work)): support.sha(p.read_bytes())
              for directory in [work, proof] for p in directory.iterdir() if p.is_file() and p.suffix in ['.v', '.vo', '.log']},
          'tools_sha256': {n: support.sha((HERE / n).read_bytes()) for n in ['finish.py', 'check-source.py', 'test-source.py']},
          'normal_registration': False, 'coverage_added': 0}
support.changed({HERE / 'REVIEW.json': json.dumps(record, indent=2) + '\n',
                 HERE / 'source/jet_elements_tapleaf_literal.v.source': source.read_text(),
                 HERE / 'contracts.log': report, HERE / 'assumptions.log': (work / 'assumptions.log').read_text()})
print('Actual-C tapleaf-version literal contract compiled, fully printed, source-reviewed and recursively kernel-checked; registry unchanged')
