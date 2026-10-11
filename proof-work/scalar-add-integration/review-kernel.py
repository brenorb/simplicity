"""Verify terminal normal kernel evidence; not full acceptance."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def review():
    evidence = json.loads((archive / 'PREPARATION.json').read_text())
    kernel = evidence['normal_kernel']
    if (kernel['status'] != 'terminal' or kernel['exit_code'] != 0
            or kernel['session'] != 86561 or kernel['checked_modules'] != 24):
        raise ValueError('normal kernel check is not terminal-successful')
    candidate = Path(evidence['candidate']) / 'Coq'
    load('normal_scalar_add_frozen_review', archive / 'review-normal.py').review(preliminary=True)
    actual = load('normal_scalar_add_inputs', candidate / 'jet-audit-inputs.py').fingerprint(
        candidate, archive.parent.parent)
    if actual != evidence['candidate_preacceptance_fingerprint']:
        raise ValueError('candidate inputs changed after kernel check')
    path = Path(kernel['log'])
    if hashlib.sha256(path.read_bytes()).hexdigest() != kernel['log_sha256']:
        raise ValueError('normal kernel output changed')
    text = path.read_text()
    for label in ['Constants/Inductives relying on type-in-type: <none>',
                  'Constants/Inductives relying on unsafe (co)fixpoints: <none>',
                  'Inductives whose positivity is assumed: <none>']:
        if text.count(label) != 1:
            raise ValueError('nonempty/missing unsafe category')
    if text.count('CONTEXT SUMMARY') != 1 or text.count('* Axioms:') != 1:
        raise ValueError('missing/duplicate kernel context')
    axioms = text.split('* Axioms:', 1)[1].split('* Constants/Inductives', 1)[0].split()
    inherited = (candidate / 'C/jet_coqchk_axioms.expected').read_text().splitlines()
    if sorted(axioms) != sorted(inherited) or len(axioms) != 15:
        raise ValueError('normal kernel context differs from inherited allowlist')
    return {'checked_normal_modules': 24, 'new_results': 79,
            'kernel_session': 86561, 'kernel_exit_code': 0, 'context_axioms': 15,
            'unsafe_categories_empty': True, 'source_evidence_unchanged': True,
            'audit_input_sha256': actual, 'kernel_log_sha256': kernel['log_sha256'],
            'full_acceptance': False, 'checkout_coverage_added': 0}


if __name__ == '__main__':
    print(json.dumps(review(), indent=2))
