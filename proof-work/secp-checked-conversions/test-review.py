"""In-memory corruption and proof-escape scanner fixtures; no bad proofs run."""
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('conversion_review_tests', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
policy = review.gate.load('conversion_policy_tests', HERE / 'preservation.py')
work = Path(sys.argv[1]).resolve()
review.validate(work)
raw_text, raw_bytes = Path.read_text, Path.read_bytes


def mutation(path, transform):
    original = raw_text(path)
    altered = transform(original)
    assert original != altered
    def text(self, *args, **kwargs):
        return altered if self == path else raw_text(self, *args, **kwargs)
    def binary(self, *args, **kwargs):
        return altered.encode() if self == path else raw_bytes(self, *args, **kwargs)
    with patch.object(Path, 'read_text', text), patch.object(Path, 'read_bytes', binary):
        try:
            review.validate(work)
        except (ValueError, KeyError):
            return
        raise AssertionError('accepted corrupted conversion evidence: ' + str(path))


def field(key, value):
    def change(text):
        data = json.loads(text)
        data[key] = value
        return json.dumps(data)
    return change


receipt = work / 'REVIEW.json'
for key, value in [('assembly_sha256', 'bad'), ('coverage_added', 1),
                   ('normal_registration', True), ('results', []),
                   ('dependencies', {}), ('evidence_sha256', {})]:
    mutation(receipt, field(key, value))
for key in ['build', 'assumptions', 'contracts', 'kernel']:
    def nonzero(text, key=key):
        data = json.loads(text)
        data[key]['exit_code'] = 1
        return json.dumps(data)
    mutation(receipt, nonzero)
def unsafe(text):
    data = json.loads(text)
    data['kernel']['command'].append('-norec')
    return json.dumps(data)
mutation(receipt, unsafe)
mutation(work / 'ASSEMBLY.json', field('roots', []))
mutation(work / 'ASSEMBLY.json', field('modules', []))
mutation(work / 'Coq/C/jet_secp_fe_nv.v', lambda text: text + '\n(* changed *)\n')
mutation(work / 'Coq/C/jet_frame_constructible_secp.v', lambda text: text.replace('Vint Int.one', 'Vint Int.zero'))
mutation(work / 'contracts.log', lambda text: text + '\n...\n')
mutation(work / 'kernel.log', lambda text: text + '\nCORRUPTION\n')
mutation(work / 'Coq/Simplicity/Word.v', lambda text: text + '\n(* changed canonical source *)\n')
print('18 conversion proof/evidence corruptions rejected')

# Exercise precisely the proposed normal scanner before installation. None
# of the rejected source strings is sent to Coq or written to a .v file.
changes = policy.transformations(review.REPO)
scanner = {'__name__': 'isolated_scanner_fixtures'}
exec(compile(changes['Coq/scan-jet-proofs.py'][1], 'proposed_scanner', 'exec'), scanner)
bad_sources = [
    'Lemma bad : True. Proof. vm_cast_no_check I. Qed.',
    'Lemma bad : True. Proof. native_cast_no_check I. Qed.',
    'Lemma bad : True. Proof. Admitted.', 'Local Axiom bad : False.',
    '#[local] Axiom bad : False.', 'Lemma bad : True. Proof. admit. Qed.',
    'Lemma bad : True. Proof. give_up. Qed.', 'Lemma bad : True. Proof. Abort.',
    'Unset Guard Checking.', 'Unset Universe Checking.', 'Unset Positivity Checking.',
    '#[bypass_check(guard)] Fixpoint bad : nat := bad.',
]
for source in bad_sources:
    assert scanner['violations'](source), source
for source in ['Lemma good : True. Proof. exact I. Qed.',
               'Lemma good : 1 = 1. Proof. vm_compute; reflexivity. Qed.',
               '(* vm_cast_no_check (* native_cast_no_check *) *)',
               'Definition label := "Admitted. ""vm_cast_no_check""".']:
    assert not scanner['violations'](source), source
print('12 proof-escape fixtures rejected; checked computation, comments and strings retained')
review.validate(work)
