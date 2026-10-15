"""Explicit, hash-checked successor to older additive-only input baselines.

The older baseline is not rewritten. Only these exact reviewed proof repairs
and the scanner/test strengthening can supersede its original source hashes.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = '87e9ad7b'
REPAIRS = {'jet_secp_fns': ['secp_pure_lookup'], 'jet_secp_fe_nv': ['nv_run_eq'],
           'jet_secp_fe_b32': ['sb_run_eq', 'gb_run_eq']}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def transformations(repo):
    result = {}
    for name, lemmas in REPAIRS.items():
        path = 'Coq/C/' + name + '.v'
        before = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo).decode()
        after = before
        for lemma in lemmas:
            pattern = r'(\bLemma ' + lemma + r'\b.*?\bProof\.)\s*vm_cast_no_check\s+.*?\bQed\.'
            after, count = re.subn(pattern, r'\1 timeout 10 (vm_compute; reflexivity). Qed.', after, flags=re.S)
            if count != 1:
                raise ValueError('unexpected frozen conversion source')
        result[path] = (before, after)
    path = 'Coq/scan-jet-proofs.py'
    before = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo).decode()
    old = r'|bypass_check)\b'
    new = r'|bypass_check|vm_cast_no_check|native_cast_no_check)\b'
    if before.count(old) != 1:
        raise ValueError('unexpected frozen scanner')
    result[path] = (before, before.replace(old, new))
    path = 'Coq/test-jet-gates.py'
    before = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo).decode()
    old = '            "Unset Guard Checking.",\n'
    new = ('            "Lemma cheat : True. Proof. vm_cast_no_check I. Qed.",\n'
           '            "Lemma cheat : True. Proof. native_cast_no_check I. Qed.",\n' + old)
    if before.count(old) != 1:
        raise ValueError('unexpected frozen gate fixtures')
    result[path] = (before, before.replace(old, new))
    return result


def apply_reviewed_repairs(expected, repo):
    here = repo / 'proof-work/secp-checked-conversions'
    path = here / 'INSTALLATION.json'
    if not path.exists():
        return expected
    ledger = json.loads(path.read_text())
    changes = transformations(repo)
    if ledger['base_commit'] != BASE or set(ledger['repairs']) != set(changes):
        raise ValueError('incorrect explicit proof repair inventory')
    updated = dict(expected)
    for name, (before, after) in changes.items():
        change = ledger['repairs'][name]
        if (change != {'before_sha256': sha(before.encode()), 'after_sha256': sha(after.encode())}
                or expected.get(name) != change['before_sha256']
                or (repo / name).read_text() != after):
            raise ValueError('unreviewed existing-source modification: ' + name)
        updated[name] = change['after_sha256']
    return updated


def linked_driver_matches(recorded, repo):
    """Retain the historical driver pin across exactly the preservation hooks.

    No proof/build/audit logic is discarded. Unknown driver edits or receipt
    hashes still fail. New audits may pin the current complete driver instead.
    """
    path = 'proof-work/linked-repair/run.py'
    current = (repo / path).read_bytes()
    if recorded == sha(current):
        return True
    original = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=repo)
    if recorded != sha(original):
        return False
    text = original.decode()
    old = '    if expected != old.input_map():\n'
    new = ('    policy = old.load(\'linked_checked_conversion_policy\', REPO / \'proof-work/secp-checked-conversions/preservation.py\')\n'
           '    expected = policy.apply_reviewed_repairs(expected, REPO)\n' + old)
    clause = "            or receipt['driver_sha256'] != old.sha(Path(__file__).read_bytes())\n"
    replacement = ("            or not old.load('linked_historical_driver_policy',\n"
                   "                            REPO / 'proof-work/secp-checked-conversions/preservation.py').linked_driver_matches(\n"
                   "                                receipt['driver_sha256'], REPO)\n")
    if text.count(old) != 1 or text.count(clause) != 1:
        return False
    return current.decode() == text.replace(old, new).replace(clause, replacement)
