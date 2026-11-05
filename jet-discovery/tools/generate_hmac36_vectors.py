#!/usr/bin/env python3
"""One complete published BIP47 mask and20 independent derived width controls."""
import csv
import hashlib
import hmac
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'vendor-specs/transport-crypto'
def main():
    source=ROOT/'vendor-specs/bitcoin-growth7/bip47-hmac-order-comparison.json'
    published=json.loads(source.read_text())
    key=bytes.fromhex(published['outpoint_raw36']);data=bytes.fromhex(published['ecdh_x32'])
    assert hmac.new(key,data,hashlib.sha512).hexdigest()==published['published_mask64']
    rows=[('published-bip47-mask',key.hex(),data.hex(),published['published_mask64'])]
    for i,index in enumerate([0,1,255,256,65535,65536,2**31-1,2**31,2**32-2,2**32-1]):
        for little in [False,True]:
            key=hashlib.sha256(('key36-'+str(i)).encode()).digest()+index.to_bytes(4,'little' if little else 'big')
            data=hashlib.sha256(('data32-'+str(i)).encode()).digest()
            rows.append((f'derived-{i}-{little}',key.hex(),data.hex(),hmac.new(key,data,hashlib.sha512).hexdigest()))
    path=OUT/'hmac-sha512-36x32-vectors.tsv'
    with path.open('w',newline='')as f:
        w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['case','key_raw36_hex','data_raw32_hex','hmac64_hex']);w.writerows(rows)
    record={'published_cases':1,'derived_cases':20,'reference':'Python stdlib hmac/hashlib.sha512','published_source':str(source.relative_to(ROOT)),'published_source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'output_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'scope':'Exact raw36-byte key/raw32-byte data; word32 encoding tests do not impose Bitcoin numeric index semantics.'}
    (OUT/'hmac-sha512-36x32-manifest.json').write_text(json.dumps(record,indent=2)+'\n')
    print('one published BIP47 mask and20 derived width/byte-order controls')
if __name__=='__main__':main()
