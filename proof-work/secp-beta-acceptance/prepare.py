"""Combine checked ordinary proofs in a distinct registration candidate.

All prior registrations and frozen targets are retained. No current checkout
registry, pending index, historical checked tree or receipt is modified.
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
sp = importlib.util.spec_from_file_location('beta_acceptance_parent', HERE.parent / 'secp-beta-integration/verify.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
s, a = v.s, v.a
field = s.load('beta_acceptance_field_support', HERE.parent / 'secp-field-acceptance/prepare.py')
once = field.once


def append_missing(path, rows):
    original = path.read_text()
    old = {tuple(line.split()) for line in original.splitlines() if line.strip() and not line.startswith('#')}
    missing = [row for row in rows if tuple(row) not in old]
    return original.rstrip() + '\n' + '\n'.join(' '.join(row) for row in missing) + '\n', len(missing)


def beta_changes(work, report):
    coq, updates = work / 'Coq', {}
    path = coq / 'jet-coverage.py'
    updates[path] = once(path.read_text(), '        elif family == "bitcoin":',
        '''            elif name == "simplicity_fe_multiply_beta":
                # Exact initialized original-C/literal target, never arbitrary Ready.
                contract = (r"\\bsecp_jet_initialized_local_spec\\s+beta_initialized\\s+"
                            r"f_simplicity_fe_multiply_beta\\s+\\(Word\\s+8\\)\\s+\\(Word\\s+8\\)\\s+"
                            r"\\(@literal_fe_multiply_beta\\s+Alg\\.CoreFunSem\\)\\s*\\.$")
        elif family == "bitcoin":''')
    fixture = '''        # Beta metadata mutations are parser-only fixtures, not compiled proofs.
        beta = project / "C/jet_secp_beta_local.v"
        beta_original = beta.read_text()
        declaration = "Theorem fe_multiply_beta_initialized_local_spec :"
        start = beta_original.index(declaration)
        for old, new in (
            ("local_spec beta_initialized", "local_spec (fun _ => True)"),
            ("local_spec beta_initialized", "local_spec another_initialized_state"),
            ("f_simplicity_fe_multiply_beta (Word", "f_simplicity_fe_square (Word"),
            ("f_simplicity_fe_multiply_beta (Word", "f_read_fe (Word"),
            ("secp_jet_initialized_local_spec beta_initialized", "secp_jet_local_spec"),
            (declaration, declaration + " False ->"),
            ("(Word 8) (Word 8)", "(Word 7) (Word 8)"),
            ("(Word 8) (Word 8)", "(Word 8) (Word 7)"),
            ("(@literal_fe_multiply_beta Alg.CoreFunSem)", "(fun a => a)"),
            ("(@literal_fe_multiply_beta Alg.CoreFunSem).", "(@literal_fe_multiply_beta Alg.CoreFunSem) -> True."),
        ):
            assert old in beta_original[start:]
            beta.write_text(beta_original[:start] + beta_original[start:].replace(old, new, 1))
            rejects(coverage.inventory, "not a direct canonical jet theorem")
        beta.write_text(beta_original)
        audit = project / "C/jet_public_theorems.txt"
        audit_original = audit.read_text()
        manifest.write_text(original.replace("C.jet_secp_beta_local fe_multiply_beta_initialized_local_spec",
            "C.jet_secp_beta_from_reader eval_beta_from_reader_storage"))
        audit.write_text(audit_original.replace("C.jet_secp_beta_local fe_multiply_beta_initialized_local_spec",
            "C.jet_secp_beta_from_reader eval_beta_from_reader_storage"))
        helper = project / "C/jet_secp_beta_from_reader.v"
        helper.write_text("Theorem eval_beta_from_reader_storage : True.\\nProof. exact I. Qed.\\n")
        rejects(coverage.inventory, "not a direct canonical jet theorem")
        audit.write_text(audit_original)
        manifest.write_text(original)
        assert coverage.inventory() == rows
'''
    path = coq / 'test-jet-coverage.py'
    updates[path] = once(path.read_text(), '        # Free cached hashes are auxiliary', fixture + '        # Free cached hashes are auxiliary')
    path = coq / 'C/jet_public_theorems.txt'
    updates[path], nr = append_missing(path, [name.rsplit('.', 1) for name in report['results']])
    path = coq / 'C/jet_contract_definitions.txt'
    updates[path], nd = append_missing(path, [name.rsplit('.', 1) for name in report['definitions']] +
        [['C.jet_secp_initialized_contract', 'secp_jet_initialized_local_spec']])
    path = coq / 'C/jet_coverage.tsv'
    updates[path], nc = append_missing(path, [['simplicity_fe_multiply_beta', *report['endpoint'].rsplit('.', 1)]])
    if nr != 107 or nc != 1:
        raise ValueError('unexpected new beta audit/coverage inventory')
    # Keep every new module out of the global contract printer's import scope.
    path = coq / 'audit-jet-contracts.sh'
    text = path.read_text().replace('/^C\\.jet_secp_multiply_/',
        '/^C\\.(jet_secp_multiply_|jet_secp_beta_|jet_clight_internal_|jet_borrowed_region$)/')
    if text == path.read_text():
        raise ValueError('missing established namespace-preservation rule')
    updates[path] = text
    updates[coq / 'beta-review/check-source.py'] = (HERE / 'check-source.py.source').read_text()
    updates[coq / 'beta-review/test-source.py'] = '''import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sp = importlib.util.spec_from_file_location('beta_source_gate', Path(__file__).with_name('check-source.py'))
gate = importlib.util.module_from_spec(sp)
sp.loader.exec_module(gate)
gate.test()
'''
    path = coq / 'check-jets.sh'
    updates[path] = once(path.read_text(), 'python3 check-bitcoin-primitive-identity.py',
        'python3 beta-review/check-source.py\npython3 beta-review/test-source.py\npython3 check-bitcoin-primitive-identity.py')
    return updates, nr, nd


def main():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('beta registration candidate already prepared; reuse its recorded path')
    v.check()
    verified = subprocess.run([sys.executable, '-B', str(HERE.parent / 'check-sealed-jet-bases.py'), 'field'],
        cwd=REPO, env=s.ENV, text=True, capture_output=True, timeout=60)
    if verified.returncode:
        raise ValueError('sealed ordinary multiplication basis is unavailable: ' + verified.stdout + verified.stderr)
    base, report = v.reported()
    before, staged = s.input_map(), s.index_hash()
    fingerprint = s.inputs.fingerprint(base / 'Coq', base)
    work = Path(tempfile.mkdtemp(prefix='jet-beta-acceptance-', dir='/private/tmp'))
    subprocess.run(['cp', '-R', str(base / 'Coq'), str(base / 'C'), str(base / 'Haskell'), str(work)], check=True)
    if s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('copied beta candidate differs from checked parent')
    fprep = json.loads((HERE.parent / 'secp-field-integration/PREPARATION.json').read_text())
    fbase = Path(fprep['candidate'])
    inherited = {}
    additions = {}
    for name, row in fprep['sources'].items():
        source = fbase / name
        if s.sha(source.read_bytes()) != row['sha256']:
            raise ValueError('ordinary field source changed: ' + name)
        target = work / name
        if target.exists():
            if target.read_bytes() != source.read_bytes():
                raise ValueError('checked proof closures conflict: ' + name)
        else:
            additions[target] = source.read_text()
            inherited[name] = row['sha256']
    if len(inherited) != 10:
        raise ValueError('unexpected extra ordinary field closure')
    for project in ['_CoqProject', '_CoqProject.jets']:
        path = work / 'Coq' / project
        text = path.read_text()
        missing = [name.removeprefix('Coq/') for name in sorted(inherited) if name.removeprefix('Coq/') not in text.splitlines()]
        additions[path] = text.rstrip() + '\n' + '\n'.join(missing) + '\n'
    s.changed(additions)
    freport = json.loads((HERE.parent / 'secp-field-integration/REPORTED.json').read_text())
    updates = field.changes(work, freport)
    delta = {str(path.relative_to(work)): dict(before=s.sha(path.read_bytes()) if path.exists() else None,
        after=s.sha(code.encode())) for path, code in additions.items()}
    for path, code in updates.items():
        delta[str(path.relative_to(work))] = dict(before=s.sha(path.read_bytes()) if path.exists() else None, after=s.sha(code.encode()))
    s.changed(updates)
    beta, nr, nd = beta_changes(work, report)
    for path, code in beta.items():
        key = str(path.relative_to(work))
        delta.setdefault(key, dict(before=s.sha(path.read_bytes()) if path.exists() else None))['after'] = s.sha(code.encode())
    s.changed(beta)
    if s.inputs.fingerprint(base / 'Coq', base) != fingerprint or before != s.input_map() or staged != s.index_hash():
        raise ValueError('historical checked parent or main checkout/staging changed')
    rows = [line for line in (work / 'Coq/C/jet_coverage.tsv').read_text().splitlines() if line.strip() and not line.startswith('#')]
    if len(rows) != 351:
        raise ValueError('expected 349 retained entries plus multiplication and beta candidates')
    r = dict(candidate=str(work), parent_candidate=str(base), parent_input_sha256=fingerprint,
        parent_checked_sha256=s.sha((HERE.parent / 'secp-beta-integration/CHECKED.json').read_bytes()),
        field_checked_sha256=s.sha((HERE.parent / 'secp-field-integration/CHECKED.json').read_bytes()),
        input_sha256=s.inputs.fingerprint(work / 'Coq', work), changed_inputs=delta,
        inherited_extra_sources=inherited, combined_checked_source_modules=259,
        prepare_sha256=s.sha(Path(__file__).read_bytes()), gate_sha256=s.sha((HERE / 'check-source.py.source').read_bytes()),
        main_inputs=before, staged_patch_sha256=staged, candidate_registrations_before=349,
        candidate_registrations_after=351, new_beta_audited_results=nr, new_beta_contract_definitions=nd,
        snapshot_generation_complete=False, accepted=False, accepted_coverage_added=0)
    s.changed({HERE / 'PREPARATION.json': json.dumps(r, indent=2) + '\n'})
    print('Prepared isolated 351-entry multiplication/beta registration candidate: ' + str(work), flush=True)


if __name__ == '__main__':
    main()
