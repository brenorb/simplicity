#!/usr/bin/env python3
"""Inventory the full pinned BOLT12 JSON set and extract every signature core.

The five payer-proof valid vectors supply published full invoice transcripts,
not five complete valid payment routes or native spending transactions.
"""
import csv
import json
import re
from pathlib import Path
root=Path(__file__).resolve().parents[1]
packet=root/'vendor-specs/bitcoin-growth2'
def write(name,columns,rows):
    with(packet/name).open('w',newline='')as out:
        w=csv.writer(out,delimiter='\t',lineterminator='\n');w.writerow(columns);w.writerows(rows)
inventory=[]
for p in sorted(packet.glob('bolts-bolt12-*.json')):
    data=json.loads(p.read_text())
    if isinstance(data,list):
        for i,row in enumerate(data):
            inventory.append([p.name,str(i),row.get('description',row.get('comment','')),str(row.get('valid','not-a-reader-vector'))])
    else:
        for category in ['valid_vectors','invalid_vectors']:
            for i,row in enumerate(data.get(category,[])):
                inventory.append([p.name,f'{category}/{i}',row.get('name',''),str(category=='valid_vectors')])
write('bolt12-all-vector-inventory.tsv',['source','case','description','source_expectation'],inventory)
cores=[]
for i,row in enumerate(json.loads((packet/'bolts-bolt12-signature-test.json').read_text())):
    fields=[]
    for leaf in row['leaves']:
        key=next(k for k in leaf if k.startswith('H(`LnLeaf`,'))
        fields.append(re.search(r',([0-9a-f]+)\)',key).group(1))
    public='-'
    if 'signature' in row:
        # The sole signature vector signs invoice_request with invreq_payer_id.
        public=next(raw[6:] for raw in fields if raw.startswith('5821'))
    cores.append([i,''.join(fields),row['merkle'],row.get('signature_tag','-'),row.get('H(signature_tag,merkle)','-'),row.get('signature','-'),public])
write('bolt12-signature-core.tsv',['case','raw_unsigned_tlvs','root','signature_tag','message','signature','public_key_x'],cores)
invoices=[]
data=json.loads((packet/'bolts-bolt12-payer-proof-test.json').read_text())
for i,row in enumerate(data['valid_vectors']):
    invoices.append([i,row['name'],row['input']['invoice_hex']])
write('bolt12-published-invoice-core.tsv',['case','name','raw_invoice_tlvs'],invoices)
assert len(cores)==4 and len(invoices)==5
print(f'Inventoried all{len(inventory)} official BOLT12 JSON rows; extracted all4 signature cores and all5 published invoice transcripts')
