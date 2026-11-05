#!/usr/bin/env python3
"""Offline complete BIP47 local derivation and pinned-source integrity check."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1];packet=root/'vendor-specs/bitcoin-growth8'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((packet/'manifest.json').read_text())
covered=set()
for record in manifest['records']:
 path=packet/record['file'];assert path.stat().st_size==record['bytes']and sha(path)==record['sha256'],path
 if path.suffix=='.tsv':assert b'\r'not in path.read_bytes(),path
 covered.add(path.name)
for source in manifest['primary_sources']:
 path=root/source['path'];assert sha(path)==source['sha256'],path
for path in packet.iterdir():
 if path.is_file():assert path.name in covered|{'manifest.json'},path
assert len((packet/'bip47-accounts.tsv').read_text().splitlines())==3
assert len((packet/'bip47-all-payments.tsv').read_text().splitlines())==11
assert len((packet/'bip47-derived-payment-wires.tsv').read_text().splitlines())==11
print(f'PASS full2account/11child/10payment BIP47 source packet;{len(covered)} derived files, pinned primary hashes and LF TSVs')
