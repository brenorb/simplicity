#!/usr/bin/env python3
"""Inventory whole upstream sets; retain complete supported cases as data."""
from pathlib import Path
import collections,csv,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1];D=ROOT/'vendor-specs/crypto-families'
def tsv(name,fields,rows):
 with(D/name).open('w',newline='')as f:
  w=csv.DictWriter(f,fields,delimiter='\t',quoting=csv.QUOTE_ALL,lineterminator='\n');w.writeheader();w.writerows(rows)
source=json.loads((D/'blake3-test_vectors_test_vectors.json').read_text())
inventory=[];supported=[]
for i,row in enumerate(source['cases']):
 n=row['input_len'];yes=n<=2048
 inventory.append(dict(case=i,input_bytes=n,modes='hash,keyed_hash,derive_key',verdict='supported_unkeyed_only'if yes else'outside_input_bound',reason='one complete unkeyed32-byte tree-hash profile; keyed/derive/XOF modes receive no extra count'if yes else'input exceeds2048-byte bound'))
 if yes:supported.append(dict(case=i,input_bytes=n,expected32=row['hash'][:64]))
tsv('blake3-inventory.tsv',['case','input_bytes','modes','verdict','reason'],inventory)
tsv('blake3-unkeyed-bounded.tsv',['case','input_bytes','expected32'],supported)

def rsp(file):
 rows=[];r={}
 for line in(D/file).read_text().splitlines()+['']:
  line=line.strip()
  if not line:
   if 'Msg'in r and 'Output'in r:rows.append(r)
   r={};continue
  if not line.startswith(('#','['))and' = 'in line:
   k,v=line.split(' = ',1);r[k]=v
 return rows
shake_inventory=[];selected=[]
for file in ['SHAKE256ShortMsg.rsp','SHAKE256LongMsg.rsp','SHAKE256VariableOut.rsp']:
 for i,row in enumerate(rsp(file)):
  bits=int(row.get('Len',256));outbits=int(row.get('Outputlen',256));msg=bytes.fromhex(row['Msg'])[:bits//8]
  assert bits%8==0 and outbits%8==0 and len(msg)==bits//8
  yes=bits<=511*8 and outbits==2000
  shake_inventory.append(dict(source=file,case=i,input_bits=bits,output_bits=outbits,verdict='complete250byte_KAT'if yes else'other_profile',reason='exact supported input and250-byte output'if yes else'full primary case retained; this corpus row fixes250-byte output and input<=511bytes'))
  if yes:selected.append(dict(source=file,case=i,message=msg.hex(),expected250=row['Output']))
tsv('shake256-inventory.tsv',['source','case','input_bits','output_bits','verdict','reason'],shake_inventory)
tsv('shake256-kat250.tsv',['source','case','message','expected250'],selected)
stats={'blake3_all_cases':len(inventory),'blake3_supported_unkeyed':len(supported),'shake256_threefile_cases':len(shake_inventory),'shake256_complete250byte_cases':len(selected),'other_zip_files':'SHAKE128 and MonteCarlo files retained in zip inventory; not claimed direct SHAKE256-250 cases.'}
(D/'kat-inventory-summary.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats,indent=2))
