"""Install only the accepted seven-jet delta, preserving the entire old index.

Both prerequisite terminal acceptances are required. Never copy compiler
objects or silently include any unrelated staged/unstaged change in a commit.
"""
import difflib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('seven_install_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support = review.gate, review.support
work = Path(sys.argv[1]).resolve()
if (HERE / 'INSTALLATION.json').exists():
    raise ValueError('one-time seven-jet installation already performed')
if not (work / 'ACCEPTANCE.json').exists():
    raise ValueError('full seven-jet acceptance has not terminated successfully; do not install')
prior_path = HERE.parent / 'elements-direct-getters-admission/MAIN-ACCEPTANCE.json'
if not prior_path.exists():
    raise ValueError('prerequisite actual-main getter acceptance is not complete')
getter = json.loads(prior_path.read_text())
getter_post = support.load('seven_install_getter_check', HERE.parent / 'elements-direct-getters-admission/post-check.py')
if getter_post.check()['actual_main_acceptance'] is not True:
    raise ValueError('prerequisite actual-main source/acceptance is not verified')
review.review(work)
accepted = json.loads((work / 'ACCEPTANCE.json').read_text())
audited = json.loads((work / 'REVIEW.json').read_text())
meta = json.loads((work / 'ASSEMBLY.json').read_text())
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if (accepted['exit_code'] != 0 or accepted['full_acceptance'] is not True or accepted['coverage'] != '378/533' or
        accepted['command'] != ['bash', 'check-jets.sh', '--accept'] or
        accepted['review_sha256'] != support.sha((work / 'REVIEW.json').read_bytes()) or
        accepted['driver_sha256'] != support.sha((HERE / 'accept.py').read_bytes()) or
        support.sha((work / 'acceptance.log').read_bytes()) != accepted['log_sha256'] or
        not (work / 'acceptance.log').read_text().rstrip().endswith(marker)):
    raise ValueError('seven-jet terminal whole-registry acceptance evidence differs')
if (support.inputs.fingerprint(work / 'Coq', work) != accepted['audit_input_sha256'] or
        accepted['audit_input_sha256'] != audited['candidate_input_sha256'] or
        getter['audit_input_sha256'] != meta['main_input_sha256']):
    raise ValueError('accepted candidate/prerequisite source identity differs')
for name, digest in audited['tools_sha256'].items():
    if support.sha((HERE / name).read_bytes()) != digest:
        raise ValueError('review tool drift')
for name, digest in audited['evidence_sha256'].items():
    if support.sha((work / name).read_bytes()) != digest:
        raise ValueError('reviewed source/object/terminal evidence drift')
paths = gate.METADATA + gate.SCRIPTS + gate.GUARDS + gate.NEW_SOURCES
if len(paths) != len(set(paths)):
    raise ValueError('duplicate installation target')
for name in gate.NEW_SOURCES + gate.GUARDS:
    if (gate.MAIN / name).exists():
        raise ValueError('new installation target already exists: ' + name)
changes = {gate.MAIN / name: (work / 'Coq' / name).read_text() for name in paths}
installed = {'Coq/' + name: support.sha((work / 'Coq' / name).read_bytes()) for name in paths}
expected = dict(meta['main_inputs'])
expected.update(installed)
ledger = {'candidate': str(work), 'installed_sha256': installed,
          'before_input_sha256': meta['main_input_sha256'], 'candidate_input_sha256': accepted['audit_input_sha256'],
          'main_staged_patch_sha256': meta['staged_patch_sha256'],
          'prior_getter_main_acceptance_sha256': support.sha(prior_path.read_bytes()),
          'isolated_acceptance_sha256': support.sha((work / 'ACCEPTANCE.json').read_bytes()),
          'coverage': '378/533', 'coverage_added': 7, 'main_installation': True, 'actual_main_acceptance': False}
delta = ''.join(line for name in paths for line in difflib.unified_diff(
    (gate.MAIN / name).read_text().splitlines(True) if (gate.MAIN / name).exists() else [],
    (work / 'Coq' / name).read_text().splitlines(True),
    fromfile=('a/Coq/' + name if (gate.MAIN / name).exists() else '/dev/null'), tofile='b/Coq/' + name))
changes[HERE / 'DELTA.patch'] = delta
changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
support.changed(changes)
if support.input_map() != expected or support.index_hash() != meta['staged_patch_sha256']:
    raise ValueError('installation changed unrelated sources or staging')
if support.inputs.fingerprint(gate.MAIN, gate.REPO) != accepted['audit_input_sha256']:
    raise ValueError('installed source is not byte-identical to accepted seven-jet candidate')
print('Seven Elements jets installed from full acceptance; exact source identity and original staging preserved; no compiler objects copied')
