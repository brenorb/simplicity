"""Install a bounded, checked secp proof repair, never registry/snapshot edits."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('install_checked_conversion_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
run, gate, REPO = review.run, review.gate, review.REPO
policy = gate.load('install_checked_conversion_policy', HERE / 'preservation.py')
work = Path(sys.argv[1]).resolve()
meta, receipt = review.validate(work)
extra = json.loads((HERE / 'EXTRA_REVIEW.json').read_text())
if (HERE / 'INSTALLATION.json').exists():
    raise ValueError('one-time installation already performed')
if gate.inputs.fingerprint(REPO / 'Coq', REPO) != meta['main_inputs_sha256']:
    raise ValueError('main inputs changed since review')
if (extra['review_sha256'] != gate.sha((work / 'REVIEW.json').read_bytes()) or
        extra['normal_registration'] is not False or extra['coverage_added'] != 0 or extra['main_installation'] is not False):
    raise ValueError('incorrect supplemental audit')
for name, digest in extra['artifact_sha256'].items():
    if gate.sha((work / name).read_bytes()) != digest:
        raise ValueError('supplemental artifact drift')
for name, digest in extra['tool_sha256'].items():
    if gate.sha((HERE / name).read_bytes()) != digest:
        raise ValueError('supplemental tool drift')
for name, digest in extra['production_input_sha256'].items():
    if gate.sha((REPO / 'Coq/C' / name).read_bytes()) != digest:
        raise ValueError('production recipe drift')
for key, command in {
    'AST': ['bash', 'C/regenerate-secp-jets.sh', str(work / 'regenerated.v')],
    'definitions': ['bash', 'build-jets.sh', '--coqc', '-q', str(work / 'definitions.v')],
    'negative_tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)],
}.items():
    evidence = extra[key]
    if evidence['command'] != command or evidence['exit_code'] != 0:
        raise ValueError('wrong supplemental command/exit status')
if (work / 'regenerated.v').read_bytes() != (REPO / 'Coq/C/jets_secp.v').read_bytes():
    raise ValueError('production AST substitution')
if (work / 'negative-tests.log').read_text().splitlines() != [
        '18 conversion proof/evidence corruptions rejected',
        '12 proof-escape fixtures rejected; checked computation, comments and strings retained']:
    raise ValueError('incomplete negative fixtures')

before = gate.input_map()
expected, changes, repairs = dict(before), {}, {}
for name, (old, new) in policy.transformations(REPO).items():
    if (REPO / name).read_text() != old:
        raise ValueError('existing source is not the reviewed clean base: ' + name)
    if name.startswith('Coq/C/') and (work / name).read_text() != new:
        raise ValueError('installed proof differs from checked candidate')
    changes[REPO / name] = new
    repairs[name] = {'before_sha256': gate.sha(old.encode()), 'after_sha256': gate.sha(new.encode())}
    expected[name] = repairs[name]['after_sha256']

new_path = 'Coq/C/jet_frame_constructible_secp.v'
if (REPO / new_path).exists():
    raise ValueError('would overwrite a preexisting constructibility module')
text = (work / new_path).read_text()
if text != (HERE / 'source/jet_frame_constructible_secp.v.source').read_text():
    raise ValueError('new source archive drift')
gate.safe_source(text, new_path)
changes[REPO / new_path] = text
added = {new_path: gate.sha(text.encode())}
expected.update(added)
ledger = {'base_commit': policy.BASE, 'repairs': repairs, 'sources': added,
          'review_sha256': gate.sha((work / 'REVIEW.json').read_bytes()),
          'extra_review_sha256': gate.sha((HERE / 'EXTRA_REVIEW.json').read_bytes()),
          'before_inputs_sha256': meta['main_inputs_sha256'],
          'staged_patch_sha256': meta['staged_patch_sha256'],
          'whole_worktree_acceptance': False, 'normal_registration': False, 'coverage_added': 0}
changes[HERE / 'INSTALLATION.json'] = json.dumps(ledger, indent=2) + '\n'
for parent in ['linked-repair', 'claude-remainder-integration']:
    changes[HERE.parent / parent / 'secp-checked-conversions/INSTALLATION.json'] = json.dumps({
        'group': 'secp-checked-conversions', 'sources': added,
        'repair_ledger': 'proof-work/secp-checked-conversions/INSTALLATION.json',
        'normal_registration': False, 'coverage_added': 0}, indent=2) + '\n'
gate.changed(changes)
if gate.input_map() != expected or gate.index_hash() != meta['staged_patch_sha256']:
    raise ValueError('unexpected main source or staging change')
gate.preservation()
review.validate(work)
print('Four checked proof replacements, scanner regression guard and secp frame constructibility installed; registry unchanged')
