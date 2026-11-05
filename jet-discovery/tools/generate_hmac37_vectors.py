#!/usr/bin/env python3
"""Independent stdlib HMAC-SHA512 KATs for exact BIP32-shaped37-byte data.

These are derived tests, not published RFC4231 cases. No external code runs.
"""
import csv
import hashlib
import hmac
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'vendor-specs/transport-crypto'


def main():
    rows = []
    patterns = [bytes(32), bytes([255])*32, bytes(range(32)),
                bytes.fromhex('873dff81c02f525623fd1fe5167eac3a55a049de3d314bb42ee227ffed37d508')]
    for i, index in enumerate([0, 1, 2, 255, 256, 65535, 65536,
                               2**31-1, 2**31, 2**32-1]):
        for prefix in [2, 3]:
            key = patterns[i % len(patterns)]
            x = hashlib.sha256(('hmac37-body-'+str(i)).encode()).digest()
            message = bytes([prefix])+x+index.to_bytes(4, 'big')
            expected = hmac.new(key, message, hashlib.sha512).hexdigest()
            rows.append((f'derived-{i}-{prefix}', key.hex(), prefix, x.hex(), index, expected))
    path = OUT / 'hmac-sha512-37-derived.tsv'
    with path.open('w', newline='') as out:
        writer = csv.writer(out, delimiter='\t', lineterminator='\n')
        writer.writerow(['case', 'key_hex', 'prefix', 'x_hex', 'index', 'hmac_hex'])
        writer.writerows(rows)
    record = {'status': 'derived KATs, not published vectors', 'cases': len(rows),
              'tool': 'tools/generate_hmac37_vectors.py',
              'reference': 'Python stdlib hmac with hashlib.sha512, RFC2104 definition',
              'scope': 'exact32-byte keys and37-byte messages; includes indices outside CKDpub policy to test hashing only',
              'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
    (OUT / 'hmac-sha512-37-derived-manifest.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'{len(rows)} independent derived HMAC-SHA512 KATs')


if __name__ == '__main__':
    main()
