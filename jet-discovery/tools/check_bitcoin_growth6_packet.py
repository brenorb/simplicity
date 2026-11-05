#!/usr/bin/env python3
"""Offline complete BIP32 source/derived packet integrity check."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1];p=root/'vendor-specs/bitcoin-growth6';m=json.loads((p/'manifest.json').read_text())
assert hashlib.sha256((p/m['primary_source']).read_bytes()).hexdigest()==m['primary_sha256']
covered=set()
for r in m['records']:
 f=p/r['file'];d=f.read_bytes();assert len(d)==r['bytes']and hashlib.sha256(d).hexdigest()==r['sha256'],f
 if f.suffix=='.tsv':assert b'\r'not in d,f
 covered.add(f.name)
for f in p.iterdir():
 if f.is_file():assert f.name in covered|{'manifest.json'},f
print(f"PASS complete pinned BIP32 source hash and{len(covered)} local derived files; all LF TSVs")
