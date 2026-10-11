"""Read-only fixtures for terminal kernel/fingerprint evidence."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch
sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('scalar_add_normal_kernel', archive / 'review-kernel.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


if __name__ == '__main__':
    gate.review()
    prep_path = archive / 'PREPARATION.json'
    original_text, original_bytes = Path.read_text, Path.read_bytes
    base = json.loads(original_text(prep_path))
    log_path = Path(base['normal_kernel']['log'])
    for mode in ['running', 'bad_exit', 'fingerprint', 'output_hash',
                 'unsafe', 'new_axiom', 'missing_context']:
        evidence = copy.deepcopy(base)
        changed = original_bytes(log_path)
        if mode == 'running':
            evidence['normal_kernel']['status'] = 'running'
        elif mode == 'bad_exit':
            evidence['normal_kernel']['exit_code'] = 1
        elif mode == 'fingerprint':
            evidence['candidate_preacceptance_fingerprint'] = '0' * 64
        elif mode == 'output_hash':
            changed += b'\nchanged output\n'
        elif mode == 'unsafe':
            changed = changed.replace(b'type-in-type: <none>', b'type-in-type: unsafe')
        elif mode == 'new_axiom':
            changed = changed.replace(b'compcert.x86_64.Archi.win64', b'Untrusted.kernel_axiom')
        elif mode == 'missing_context':
            changed = changed.replace(b'CONTEXT SUMMARY', b'MISSING SUMMARY')
        if mode in {'unsafe', 'new_axiom', 'missing_context'}:
            evidence['normal_kernel']['log_sha256'] = hashlib.sha256(changed).hexdigest()

        def read_text(p, *args, **kwargs):
            if p == prep_path:
                return json.dumps(evidence)
            if p == log_path:
                return changed.decode()
            return original_text(p, *args, **kwargs)

        def read_bytes(p, *args, **kwargs):
            return changed if p == log_path else original_bytes(p, *args, **kwargs)

        with patch.object(Path, 'read_text', read_text), patch.object(Path, 'read_bytes', read_bytes):
            try:
                gate.review()
            except ValueError:
                pass
            else:
                raise AssertionError('kernel mutation accepted: ' + mode)
    gate.review()
    print('normal kernel receipt matches; seven status/hash/fingerprint/context mutations rejected')
