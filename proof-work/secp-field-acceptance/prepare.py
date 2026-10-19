"""Prepare an isolated registration candidate from the checked regular build.

Never edits the checkout's pending registry/index or the historical checked
tree. Existing registrations are retained, not silently removed to pass tests.
Snapshot generation and successful acceptance are separate later phases.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sp = importlib.util.spec_from_file_location('field_acceptance_parent', HERE.parent / 'secp-field-integration/verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, a = v.s, v.a


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError('missing/ambiguous support-edit anchor: ' + old)
    return text.replace(old, new, 1)


def changes(work, report):
    coq = work / 'Coq'
    result = {}
    p = coq / 'jet-coverage.py'
    result[p] = once(p.read_text(), '        elif family == "bitcoin":',
        '''            elif name == "simplicity_fe_multiply":
                # Full original public function, unrestricted Word256 pair,
                # literal Simplicity program: no helper/numeric replacement.
                contract = (r"\\bsecp_jet_local_spec\\s+f_simplicity_fe_multiply\\s+"
                            r"\\(Ty\\.Prod\\s+\\(Word\\s+8\\)\\s+\\(Word\\s+8\\)\\)\\s+\\(Word\\s+8\\)\\s+"
                            r"\\(@literal_fe_multiply\\s+Alg\\.CoreFunSem\\)\\s*\\.$")
        elif family == "bitcoin":''')
    p = coq / 'test-jet-coverage.py'
    fixture = '''        # FeMultiply must be the exact complete original-C/literal contract.
        multiply = project / "C/jet_secp_multiply_literal_jet.v"
        multiply_original = multiply.read_text()
        declaration = "Theorem fe_multiply_literal_local_spec :"
        start = multiply_original.index(declaration)
        for old, new in (
            ("secp_jet_local_spec f_simplicity_fe_multiply", "secp_jet_local_spec f_read_fe"),
            ("secp_jet_local_spec f_simplicity_fe_multiply", "secp_jet_local_spec f_simplicity_fe_square"),
            ("secp_jet_local_spec f_simplicity_fe_multiply", "jet_local_spec f_simplicity_fe_multiply"),
            (declaration, declaration + " False ->"),
            ("(Ty.Prod (Word 8) (Word 8)) (Word 8)", "(Ty.Prod (Word 7) (Word 7)) (Word 8)"),
            ("(Ty.Prod (Word 8) (Word 8)) (Word 8)", "(Ty.Prod (Word 8) (Word 8)) (Word 7)"),
            ("(Ty.Prod (Word 8) (Word 8)) (Word 8)", "(Ty.Sum (Word 8) (Word 8)) (Word 8)"),
            ("(@literal_fe_multiply Alg.CoreFunSem)", "(@input_product_word Alg.CoreFunSem)"),
            ("(@literal_fe_multiply Alg.CoreFunSem)", "(fun a => a)"),
            ("(@literal_fe_multiply Alg.CoreFunSem).", "(@literal_fe_multiply Alg.CoreFunSem) -> True."),
        ):
            assert old in multiply_original[start:]
            multiply.write_text(multiply_original[:start] + multiply_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        multiply.write_text(multiply_original)
        manifest.write_text(original.replace("C.jet_secp_multiply_literal_jet fe_multiply_literal_local_spec",
            "C.jet_secp_multiply_literal_jet eval_original_public_field_multiply_literal"))
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        manifest.write_text(original)
        assert coverage.inventory() == rows
'''
    result[p] = once(p.read_text(), '        # Free cached hashes are auxiliary', fixture + '        # Free cached hashes are auxiliary')
    for name, additions in [
        ('jet_public_theorems.txt', [n.rsplit('.', 1) for n in report['results']]),
        ('jet_contract_definitions.txt', [n.rsplit('.', 1) for n in report['definitions']] +
            [['C.jet_secp_negate_literal_contract', n] for n in ['literal_fe_normalize512', 'literal_fe_multiply']]),
        ('jet_coverage.tsv', [['simplicity_fe_multiply', report['public_contract'].rsplit('.', 1)[0],
                              report['public_contract'].rsplit('.', 1)[1]]]),
    ]:
        p = coq / 'C' / name
        original = p.read_text()
        old = {tuple(l.split()) for l in original.splitlines() if l.strip() and not l.startswith('#')}
        if any(tuple(row) in old for row in additions):
            raise ValueError('registration already present: ' + name)
        result[p] = original.rstrip() + '\n' + '\n'.join(' '.join(row) for row in additions) + '\n'
    # Avoid opening the new helper modules in the global contract-printing
    # namespace. Old theorem imports and checks remain byte-for-byte unchanged.
    p = coq / 'audit-jet-contracts.sh'
    text = once(p.read_text(), '         {print "Require Import " $0 "."}',
        '         /^C\\.jet_secp_multiply_/ {print "Require " $0 "."; next}\n         {print "Require Import " $0 "."}')
    text = once(text, 'printf "Check %s.%s.\\n", $1, $2',
        'printf "Check %s%s.%s.\\n", ($1 ~ /^C\\.jet_secp_multiply_/ ? "@" : ""), $1, $2')
    result[p] = text
    # Preserve and install the already checked nine source-gate/reference blobs.
    archive_map = json.loads(a.blob('proof-work/secp-field-literal/ARCHIVED-INPUTS.json'))['inputs']
    for original, row in archive_map.items():
        if original.startswith('Coq/negate-review/'):
            raw = a.blob('proof-work/secp-field-literal/' + row['archive'])
            if s.sha(raw) != row['sha256']:
                raise ValueError('source-gate archive hash changed')
            result[work / original] = raw.decode()
    # Same scoped catalog/literal/full-contract checker and ten mutations,
    # reading the regular module, with local Coq and canonical repo separated.
    gate = a.blob('proof-work/secp-field-literal/check-source.py').decode()
    gate = once(gate, 'import importlib.util', 'import importlib.util\nimport os')
    gate = once(gate, 'REPO = HERE.parents[1]',
        'COQ = HERE.parent\nREPO = Path(os.environ.get("JET_C_REPO", HERE.parents[1]))')
    gate = gate.replace("REPO / 'Coq/", "COQ / '")
    gate = once(gate, "(HERE / 'Jet.v.source')", "(COQ / 'C/jet_secp_multiply_literal_jet.v')")
    gate = once(gate, "if __name__ == '__main__':\n    test()",
        "if __name__ == '__main__':\n    check(sources())\n    print('FeMultiply original catalog, literal term and full public contract match')")
    result[coq / 'multiply-review/check-source.py'] = gate
    result[coq / 'multiply-review/test-source.py'] = '''import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True
p = Path(__file__).with_name('check-source.py')
sp = importlib.util.spec_from_file_location('multiply_source_gate', p)
gate = importlib.util.module_from_spec(sp)
sp.loader.exec_module(gate)
gate.test()
'''
    p = coq / 'check-jets.sh'
    gate_calls = '''for gate in negate-wiring recursive-ports literal-ports foundations; do
  candidate_ports=C
  if [[ "$gate" == recursive-ports ]]; then candidate_ports=negate-review; fi
  python3 "negate-review/check-$gate.py" --repo "${JET_C_REPO:-..}" --candidates "$candidate_ports"
  python3 "negate-review/test-$gate.py" --repo "${JET_C_REPO:-..}" --candidates "$candidate_ports"
done
python3 multiply-review/check-source.py
python3 multiply-review/test-source.py
'''
    result[p] = once(p.read_text(), 'python3 check-bitcoin-primitive-identity.py',
        gate_calls + 'python3 check-bitcoin-primitive-identity.py')
    return result


def main():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('acceptance candidate already prepared; use its recorded path')
    v.check()
    base, prior, _ = v.reported()
    before, staged = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(base / 'Coq', base)
    work = Path(tempfile.mkdtemp(prefix='jet-field-acceptance-', dir='/private/tmp'))
    subprocess.run(['cp', '-R', str(base / 'Coq'), str(base / 'C'), str(base / 'Haskell'), str(work)], check=True)
    if s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('candidate copy differs from checked regular tree')
    report = json.loads((HERE.parent / 'secp-field-integration/REPORTED.json').read_text())
    updates = changes(work, report)
    delta = {str(p.relative_to(work)): dict(before=s.sha(p.read_bytes()) if p.exists() else None,
        after=s.sha(code.encode())) for p, code in updates.items()}
    s.changed(updates)
    if s.inputs.fingerprint(base / 'Coq', base) != fingerprint or s.input_map() != before or s.index_hash() != staged:
        raise ValueError('historical candidate/checkout/staged inputs changed')
    r = dict(candidate=str(work), parent_candidate=str(base), parent_input_sha256=fingerprint,
        parent_checked_sha256=s.sha((HERE.parent / 'secp-field-integration/CHECKED.json').read_bytes()),
        input_sha256=s.inputs.fingerprint(work / 'Coq', work), changed_inputs=delta,
        prepare_sha256=s.sha(Path(__file__).read_bytes()), main_inputs=before, staged_patch_sha256=staged,
        candidate_registrations_before=349, candidate_registrations_after=350,
        new_audited_results=413, new_contract_definitions=299,
        snapshot_generation_complete=False, accepted=False, accepted_coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared full registration candidate ' + str(work) + '; prior tree and checkout unchanged', flush=True)


if __name__ == '__main__':
    main()
