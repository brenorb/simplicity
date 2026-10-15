"""Install only exact reviewed metadata after terminal isolated acceptance.

Existing staged changes are never added, reset or committed. Proof/C/Haskell
sources and compiler outputs are untouched. Actual-main acceptance is separate.
"""
import importlib.util
import difflib
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_install_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support, REPO = review.gate, review.support, review.REPO
work = Path(sys.argv[1]).resolve()
review.review(work)
if (HERE / 'INSTALLATION.json').exists():
    raise ValueError('one-time admission installation already performed')
accepted = json.loads((work / 'ACCEPTANCE.json').read_text())
audited = json.loads((work / 'REVIEW.json').read_text())
meta = json.loads((work / 'ASSEMBLY.json').read_text())
if (accepted['exit_code'] != 0 or accepted['full_acceptance'] is not True or
        accepted['coverage'] != '366/533' or accepted['command'] != ['bash', 'check-jets.sh', '--accept'] or
        accepted['review_sha256'] != support.sha((work / 'REVIEW.json').read_bytes()) or
        support.sha((work / 'acceptance.log').read_bytes()) != accepted['log_sha256'] or
        not (work / 'acceptance.log').read_text().rstrip().endswith(
            'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)')):
    raise ValueError('missing/altered terminal whole-registry acceptance')
if (support.inputs.fingerprint(work / 'Coq', work) != accepted['audit_input_sha256'] or
        accepted['audit_input_sha256'] != audited['candidate_input_sha256']):
    raise ValueError('accepted candidate input drift')
for name, digest in audited['tools_sha256'].items():
    if support.sha((HERE / name).read_bytes()) != digest:
        raise ValueError('review tool drift')
for name, digest in audited['evidence_sha256'].items():
    if support.sha((work / name).read_bytes()) != digest:
        raise ValueError('review object/evidence drift')
paths = gate.METADATA + gate.SCRIPTS + gate.GUARDS
changes = {gate.MAIN / name: (work / 'Coq' / name).read_text() for name in paths}
expected = dict(meta['main_inputs'])
installed = {'Coq/' + name: support.sha((work / 'Coq' / name).read_bytes()) for name in paths}
expected.update(installed)
ledger = {'candidate': str(work), 'installed_sha256': installed,
          'before_input_sha256': meta['main_input_sha256'],
          'candidate_input_sha256': accepted['audit_input_sha256'],
          'main_staged_patch_sha256': meta['staged_patch_sha256'],
          'isolated_acceptance_sha256': support.sha((work / 'ACCEPTANCE.json').read_bytes()),
          'coverage': '366/533', 'coverage_added': 2,
          'main_installation': True, 'actual_main_acceptance': False}
# Retain only this task's delta, not a commit of any preexisting dirty metadata.
delta = ''.join(line for name in paths for line in difflib.unified_diff(
    (gate.MAIN / name).read_text().splitlines(True) if (gate.MAIN / name).exists() else [],
    (work / 'Coq' / name).read_text().splitlines(True),
    fromfile=('a/Coq/' + name if (gate.MAIN / name).exists() else '/dev/null'),
    tofile='b/Coq/' + name))
changes[HERE / 'DELTA.patch'] = delta
changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
support.changed(changes)
if support.input_map() != expected or support.index_hash() != meta['staged_patch_sha256']:
    raise ValueError('installation changed unrelated inputs or staging')
if support.inputs.fingerprint(gate.MAIN, REPO) != accepted['audit_input_sha256']:
    raise ValueError('installed main is not source-identical to accepted candidate')
print('Two count jets installed with exact source identity; staged patch preserved; actual-main acceptance remains separate')
