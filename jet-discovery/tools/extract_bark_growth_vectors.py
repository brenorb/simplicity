#!/usr/bin/env python3
"""Extract literal public Bark data as data; never compile or execute upstream."""
import csv
import hashlib
import json
import re
from pathlib import Path
root=Path(__file__).resolve().parents[1]
packet=root/'vendor-specs/bitcoin-growth3'
source=packet/'bark-lib_src_test_util_vectors.rs.txt'
text=source.read_text()
def secret(name):
    return re.search(r'let '+name+r' = Keypair::from_str\("([0-9a-f]{64})"\)',text).group(1)
others=re.search(r'let others = \[(.*?)\];',text,re.S).group(1)
other_values=re.findall(r'"([0-9a-f]{64})"',others)
assert len(other_values)==5
secrets=[secret('round1_cosign_key'),secret('round2_cosign_key')]
secrets += [hashlib.sha256(k.encode()).hexdigest()for k in other_values]
secrets += [secret('server_cosign_key')]
raw=re.search(r'round_tx: deserialize_hex\("([0-9a-f]+)"\)',text).group(1)
expected=re.search(r'225120([0-9a-f]{64})00000000$',raw).group(1)
data={'source_file':source.name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'kind':'Literal current Bark published round root cross-check; private keys are upstream public test data',
      'revision':'5a7dbf9f2cd64dcdb65e3465080727e24dfe111d','server_secret':secret('server_key'),
      'cosign_secrets':secrets,'expiry_height':101010,'raw_round_transaction':raw,
      'expected_root_output_x':expected,'scope':'Checks exact sorted MuSig2 aggregate, minimal CLTV tapscript, TapLeaf/TapTweak and published actual round output; not the complete seven-leaf VTXO decoder or livechain evidence'}
(packet/'bark-round-root-kat.json').write_text(json.dumps(data,indent=2)+'\n')
with(packet/'bark-round-root-kat.tsv').open('w',newline='')as out:
    w=csv.writer(out,delimiter='\t',lineterminator='\n');w.writerow(['server_secret','expiry_height','expected_root_output_x','cosign_secrets']);w.writerow([data['server_secret'],101010,expected,','.join(secrets)])
print('Extracted exact published8-key Bark round root KAT; no upstream code executed')
