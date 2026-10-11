"""In-memory negative fixtures; never mutate proof or audit inputs."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('scalar_zero_review', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)


def reject(work, filename, transform, update_digest=False):
    path = work / filename
    old_bytes, old_text = Path.read_bytes, Path.read_text
    altered = transform(old_bytes(path))
    manifest_path = archive / 'manifest.json'
    manifest = json.loads(old_text(manifest_path))
    if update_digest:
        manifest['output_hashes'][filename] = hashlib.sha256(altered).hexdigest()

    def read_bytes(p, *args, **kwargs):
        return altered if p == path else old_bytes(p, *args, **kwargs)

    def read_text(p, *args, **kwargs):
        if p == path:
            return altered.decode()
        if p == manifest_path and update_digest:
            return json.dumps(manifest)
        return old_text(p, *args, **kwargs)

    with patch.object(Path, 'read_bytes', read_bytes), patch.object(Path, 'read_text', read_text):
        try:
            review.review(archive, work)
        except ValueError:
            return
        raise AssertionError('mutation accepted: ' + filename)


if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: test-review.py SCRATCH')
    work = Path(sys.argv[1])
    review.review(archive, work)
    reject(work, 'jet_secp_scalar_public_lifecycle.v', lambda b: b + b'\n(* source drift *)\n')
    reject(work, 'scalar_zero_public_contracts.v', lambda b: b + b'\n(* driver drift *)\n')
    reject(work, 'scalar-zero-public-assumptions.err', lambda b: b + b'Error: diagnostic\n')
    reject(work, 'scalar-zero-public-contracts.out',
           lambda b: b.replace(b'scalar_public_read_symbols\n', b'wrong_contract\n', 1), True)
    reject(work, 'scalar-zero-public-contracts.out', lambda b: b + b'\n...\n', True)
    reject(work, 'scalar-zero-public-assumptions.out',
           lambda b: b.replace(b'Axioms:\n', b'Axioms:\nUntrusted.new_axiom : True\n', 1), True)
    reject(work, 'scalar-zero-public-assumptions.out',
           lambda b: b.replace(b'JET_ASSUMPTIONS ', b'JET_ASSUMPTIONS unexpected.', 1), True)
    reject(work, 'scalar-zero-public-kernel.log',
           lambda b: b.replace(b'type-in-type: <none>', b'type-in-type: unsafe'), True)
    print('baseline passed; eight source/driver/contract/dependency/kernel mutations rejected')
