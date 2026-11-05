#!/usr/bin/env python3
"""Offline integrity and coverage check for the exact PSBT source packet."""
from pathlib import Path
import csv,hashlib,json
root=Path(__file__).resolve().parents[1];packet=root/'vendor-specs/bitcoin-growth9'
sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((packet/'manifest.json').read_text());covered=set()
for r in manifest['primary_sources']:
 data=(root/r['path']).read_bytes();assert len(data)==r['bytes']and sha(data)==r['sha256'],r['path']
for r in manifest['records']:
 path=packet/r['file'];data=path.read_bytes();assert len(data)==r['bytes']and sha(data)==r['sha256'],path
 if path.suffix=='.tsv':assert b'\r'not in data,path
 covered.add(path.name)
assert {p.name for p in packet.iterdir()if p.is_file()}==covered|{'manifest.json'}
with(packet/'psbt-all-inline-vectors.tsv').open()as f:rows=list(csv.DictReader(f,delimiter='\t'))
assert len(rows)==96 and sum(r['source']=='0174'for r in rows)==48 and sum(r['source']=='0370'for r in rows)==48
assert sum(r['base64_matches']=='true'for r in rows)==95
assert sum(r['locktime_reference']!=''and r['locktime_reference']==r['expected']for r in rows)==10
assert all(sha(bytes.fromhex(r['hex']))==r['sha256']and len(bytes.fromhex(r['hex']))==int(r['bytes'])for r in rows)
with(packet/'psbt-finalizer-derived-wires.tsv').open()as f:wires=list(csv.DictReader(f,delimiter='\t'))
assert [w['case']for w in wires]==['source','fresh']
published=[r['hex']for r in rows if r['source']=='0174'and r['ordinal']in('40','41','42')]
assert published==[wires[0][key]for key in ('partial_psbt','final_psbt','network')]
for w in wires:
 assert sha(bytes.fromhex(w['partial_psbt']))==w['partial_sha256']and sha(bytes.fromhex(w['final_psbt']))==w['final_sha256']
 assert sha(bytes.fromhex(sha(bytes.fromhex(w['network']))))==w['wtxid_raw'] and w['wtxid_raw']!=w['txid_raw']
print(f'PASS {len(covered)} derived files,3 pinned specifications,96 inline binary records,95 matching Base64 pairs,10 locktime cases and exact source/fresh wire digests')
