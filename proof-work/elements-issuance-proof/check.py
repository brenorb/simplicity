"""Kernel-check four issuance-proof C endpoints; source-fidelity review stays open."""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
spec = importlib.util.spec_from_file_location('issuance_proof_support', HERE.parent / 'elements-count/support.py')
support = importlib.util.module_from_spec(spec)
spec.loader.exec_module(support)
work = Path(sys.argv[1]).resolve()
prior_path = HERE.parent / 'elements-script-hash/PREPARATION.json'
prior = json.loads(prior_path.read_text())
base = Path(prior['candidate'])
coq, lm = work / 'Coq', 'C.jet_elements_issuance_proof_literal'
new_source = 'C/jet_elements_issuance_proof_literal.v'
if work in [base, REPO] or REPO in work.parents or (HERE / 'CHECKED.json').exists():
    raise ValueError('use a distinct unchecked external tree')
subprocess.run([sys.executable, '-B', str(HERE.parent / 'elements-script-hash/review.py')], check=True)
before, index = support.input_map(), support.index_hash()
paths = support.load('issuance_proof_paths', HERE.parent / 'elements-pegin-normal/review.py').source_paths
inherited = paths(base / 'Coq')
if (support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256'] or
        paths(coq) != inherited | {new_source}):
    raise ValueError('wrong inherited source inventory')
for n in inherited:
    if (coq / n).read_bytes() != (base / 'Coq' / n).read_bytes():
        raise ValueError('inherited source/metadata drift: ' + n)
for m in prior['fresh_modules']:
    for suffix, key in [('.v', 'source_sha256'), ('.vo', 'object_sha256')]:
        p = coq / (m.replace('.', '/') + suffix)
        if p.is_symlink() or support.sha(p.read_bytes()) != prior[key][m]:
            raise ValueError('copied checked dependency/source mismatch')
if (coq / new_source).read_bytes() != (HERE / 'source/jet_elements_issuance_proof_literal.v.source').read_bytes():
    raise ValueError('archive/checked proof mismatch')
code = support.safe_source((coq / new_source).read_text(), lm)
results = [lm + '.' + n for n in re.findall(r"^(?:Lemma|Theorem|Corollary)\s+([A-Za-z_][\w']*)", code, re.M)]
definitions = [lm + '.' + n for n in re.findall(r"^(?:Definition|Fixpoint|Record)\s+([A-Za-z_][\w']*)", code, re.M)]
if (len(results), len(definitions)) != (10, 6):
    raise ValueError('wrong issuance-proof public inventory')
originals = ['C.jet_elements_input_hash_jets.elements_issuance_' + s + '_proof_local_spec' for s in ['asset', 'token']]
originals += ['C.jet_elements_current_input_jets.elements_current_issuance_' + s + '_proof_local_spec' for s in ['asset', 'token']]
finals = [lm + '.elements_' + prefix + 'issuance_' + s + '_proof_literal_local_spec'
          for prefix in ['', 'current_'] for s in ['asset', 'token']]
fingerprint = support.inputs.fingerprint(coq, work)
commands = {}


def run(command, stem, timeout=180):
    commands[stem] = support.run(work, command, stem, timeout)


run(['bash', 'build-jets.sh', '--coqc', '-q', new_source], 'literal')
assumptions = ['Require ' + lm + '.']
contracts = assumptions + ['Set Printing All.', 'Set Printing Width 120.', 'Set Printing Depth 1000000.']
for n in results + originals:
    assumptions += ['Goal True. idtac "JET_ASSUMPTIONS ' + n + '". exact I. Qed.', 'Print Assumptions ' + n + '.']
for kind, names in [('TYPE', results), ('DEF', definitions)]:
    for n in names:
        contracts += ['Goal True. idtac "ISSUANCE_PROOF_' + kind + ' ' + n + '". exact I. Qed.',
                      ('Check @' if kind == 'TYPE' else 'Print ') + n + '.']
support.changed({work / 'assumptions.v': '\n'.join(assumptions) + '\n', work / 'contracts.v': '\n'.join(contracts) + '\n'})
for n in ['assumptions', 'contracts']:
    run(['bash', 'build-jets.sh', '--coqc', '-q', str(work / (n + '.v'))], n)
deps = support.reports.assumptions((work / 'assumptions.log').read_text())
pure = [lm + '.elements_issuance_' + s + '_proof_view_matches' for s in ['asset', 'token']]
if (set(deps) != set(results + originals) or any(not ds <= support.SIX for ds in deps.values()) or
        any(deps[n] for n in pure) or any(deps[a] != deps[b] for a, b in zip(finals, originals)) or
        any(sorted(deps[n]) != prior['dependencies'][n] for n in originals)):
    raise ValueError('new/unreviewed endpoint/primitive-view assumptions')
report = (work / 'contracts.log').read_text()
if ('...' in report or re.search(r'\?[A-Za-z]', report) or re.findall(r'(?m)^ISSUANCE_PROOF_(TYPE|DEF) (\S+)$', report) !=
        [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]):
    raise ValueError('incomplete full type/definition report')
run(['bash', 'C/check-elements-jets-generation.sh'], 'ast')
roots = ['C.jet_elements_input_hash_jets', 'C.jet_elements_current_input_jets', lm]
run(['bash', 'build-jets.sh', '--coqchk', '-silent', '-o', *roots], 'kernel', 1800)
support.kernel.kernel((work / 'kernel.log').read_text(), sorted((coq / 'C/jet_coqchk_axioms.expected').read_text().split()))
if (support.input_map() != before or support.index_hash() != index or support.inputs.fingerprint(coq, work) != fingerprint or
        support.inputs.fingerprint(base / 'Coq', base) != prior['candidate_input_sha256']):
    raise ValueError('main/index/candidate/base source drift')
r = {'candidate': str(work), 'base_candidate': str(base), 'base_input_sha256': prior['candidate_input_sha256'],
     'prior_preparation_sha256': support.sha(prior_path.read_bytes()), 'candidate_input_sha256': fingerprint,
     'main_inputs': before, 'staged_patch_sha256': index, 'new_source': new_source, 'roots': roots,
     'fresh_modules': [lm], 'reused_checked_modules': prior['fresh_modules'], 'results': results, 'definitions': definitions,
     'endpoints': finals, 'original_endpoints': originals, 'closed_view_lemmas': pure,
     'dependencies': {n: sorted(ds) for n, ds in deps.items()}, 'commands': commands,
     'source_sha256': support.sha((coq / new_source).read_bytes()), 'object_sha256': support.sha((coq / new_source).with_suffix('.vo').read_bytes()),
     'tools_sha256': {'check.py': support.sha(Path(__file__).read_bytes())},
     'source_fidelity_review_complete': False, 'normal_registration': False, 'coverage_added': 0, 'full_acceptance': False}
changes = {HERE / 'CHECKED.json': json.dumps(r, indent=2) + '\n'}
for n in ['literal.log', 'assumptions.log', 'contracts.log', 'ast.log', 'kernel.log']:
    changes[HERE / n] = (work / n).read_text()
support.changed(changes)
print('Four issuance-proof C contracts kernel-checked; canonical-source review and normal admission remain open', flush=True)
