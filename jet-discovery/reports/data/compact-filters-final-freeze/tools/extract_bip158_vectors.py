#!/usr/bin/env python3
"""Read all official BIP158 rows; parse local inert Bitcoin block bytes only."""
from pathlib import Path
import hashlib,json,csv
root=Path(__file__).resolve().parents[1]
p=root/'vendor-specs/bitcoin-growth4'
rows=json.loads((p/'bip-0158-testnet-19.json').read_text())[1:]
def compact(raw,pos):
    a=raw[pos];pos+=1
    if a<253:return a,pos
    size={253:2,254:4,255:8}[a]
    value=int.from_bytes(raw[pos:pos+size],'little')
    assert value>=({253:253,254:65536,255:4294967296}[a])
    return value,pos+size
def scripts_from_block(raw):
    n,pos=compact(raw,80);outputs=[]
    for _ in range(n):
        pos+=4
        witness=raw[pos:pos+2]==b'\x00\x01'
        if witness:pos+=2
        ni,pos=compact(raw,pos)
        for _ in range(ni):
            pos+=36;size,pos=compact(raw,pos);pos+=size+4
        no,pos=compact(raw,pos)
        for _ in range(no):
            pos+=8;size,pos=compact(raw,pos);s=raw[pos:pos+size];pos+=size
            if s and s[0]!=0x6a:outputs.append(s)
        if witness:
            for _ in range(ni):
                nw,pos=compact(raw,pos)
                for _ in range(nw):size,pos=compact(raw,pos);pos+=size
        pos+=4
    assert pos==len(raw)
    return outputs
with (p/'bip158-all-vectors.tsv').open('w',newline='')as f:
    w=csv.writer(f,delimiter='\t',lineterminator='\n')
    w.writerow(['index','height','display_block_hash','raw_header','previous_display_filter_header','raw_filter','display_filter_header','raw_unique_items','N','notes'])
    for i,row in enumerate(rows):
        height,display,block,prev_scripts,previous,filterhex,header,notes=row
        raw=bytes.fromhex(block)
        rawhash=hashlib.sha256(hashlib.sha256(raw[:80]).digest()).digest()
        assert rawhash[::-1].hex()==display
        items=sorted(set(scripts_from_block(raw)+[bytes.fromhex(s)for s in prev_scripts if s]))
        encoded=bytes.fromhex(filterhex);n,_=compact(encoded,0)
        assert n==len(items)
        w.writerow([i,height,display,raw[:80].hex(),previous,filterhex,header,','.join(s.hex()for s in items),n,notes])
print(f'PASS complete official BIP158 set: {len(rows)} rows, full block parsing/raw header hashes/all basic-filter items inventoried')
