"""Reject tampered linked receipts and escapes; preserve the candidate exactly."""
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('linked_test_driver', HERE / 'run.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)
work = Path(sys.argv[1]).resolve()
gate.review(work)

def reject(path, transform):
    original = path.read_text()
    try:
        gate.old.changed({path: transform(original)})
        try:
            gate.review(work)
        except (ValueError, KeyError, FileNotFoundError):
            return
        raise AssertionError('accepted corruption: ' + str(path))
    finally:
        gate.old.changed({path: original})


def alter(key, value):
    def apply(text):
        data = json.loads(text)
        data[key] = value
        return json.dumps(data, indent=2) + '\n'
    return apply


receipt = work / 'REVIEW.json'
assembly = work / 'ASSEMBLY.json'
for key, value in [('coverage_added', 104), ('normal_registration', True), ('source_commit', 'bad'),
                   ('assembly_sha256', 'bad'), ('driver_sha256', 'bad'), ('expected_dependencies', {}),
                   ('results', 0), ('definitions', 0), ('closed_results', 0), ('evidence_sha256', {})]:
    reject(receipt, alter(key, value))
reject(assembly, alter('roots', []))
reject(assembly, alter('modules', []))
reject(work / 'contracts.log', lambda t: t + '\n...\n')
reject(work / 'kernel.log', lambda t: t + '\nFAKE TERMINAL\n')
reject(work / 'gen-jets.py', lambda t: t + '\n# altered generator\n')
reject(work / 'Coq/C/jets.v', lambda t: t + '\n(* altered AST *)\n')

for text in ['Lemma bad : True. Admitted.', 'Axiom bad : True.', 'Parameter bad : True.',
             'Lemma bad : True. Proof. admit. Qed.',
             'Lemma bad : True. Proof. vm_cast_no_check I. Qed.',
             'Lemma bad : True. Proof. native_cast_no_check I. Qed.']:
    try:
        gate.old.safe_source(text, 'negative fixture')
    except ValueError:
        pass
    else:
        raise AssertionError('accepted proof escape')
assert 'Axioms.proof_irr' not in gate.policy('C.jet_linked_memcpy_jets.leftmost_8_1_local_spec_linked')
assert 'Axioms.proof_irr' in gate.policy('C.jet_linked_program.linked_program_is_compcert_link')
for entry in json.loads(assembly.read_text())['modules']:
    if entry['logical'] in ['C.jets_unlinked', 'C.jets_sha_unlinked']:
        assert entry['affected'], 'renamed program object must be freshly compiled'

# The copy of the canonical Coq specification has no substituted sources.
source = gate.REPO / 'Coq/Simplicity'
copy = work / 'Coq/Simplicity'
assert {p.relative_to(source) for p in source.rglob('*.v')} == {p.relative_to(copy) for p in copy.rglob('*.v')}
assert all(p.read_bytes() == (copy / p.relative_to(source)).read_bytes() for p in source.rglob('*.v'))
meta, report, _ = gate.review(work)
for n, deps in report['expected_dependencies'].items():
    if n.endswith('.linked_ast_is_compcert_link') or n.endswith('.ast_link_defs'):
        assert deps == [], 'AST-level checked link equality must be closed'
    if 'Axioms.proof_irr' in deps:
        assert 'Axioms.proof_irr' in gate.policy(n), 'unexpected link axiom inheritance'
print('Linked corruption fixtures passed: 16; lexical fixtures passed: 6; namespace/specification/link-policy checks passed')
