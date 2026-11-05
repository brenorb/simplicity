#!/usr/bin/env python3
"""Select every SHA2-128s test from a pinned official NIST prompt (data only)."""
import csv,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'vendor-specs/slhdsa'
if len(sys.argv)!=2:
 raise SystemExit('usage: extract_slh_acvp.py /path/to/official/prompt.json')
source=Path(sys.argv[1]);raw=source.read_bytes()
if hashlib.sha256(raw).hexdigest()!='4e7beb1233e47baa0acdd36417c66c45811aa40a4e32ffdb1a35d93b13b289fb':
 raise SystemExit('Prompt bytes do not match pinned official source; do not overwrite the archived subset')
prompt=json.loads(raw)
expected=json.loads((OUT/'acvp-expected-results.json').read_text())
answers={(g['tgId'],t['tcId']):t['testPassed'] for g in expected['testGroups'] for t in g['tests']}
groups=[];inventory=[];supported=[]
for group in prompt['testGroups']:
 if group['parameterSet']!='SLH-DSA-SHA2-128s':continue
 tests=[]
 for test in group['tests']:
  passed=answers[group['tgId'],test['tcId']]
  test=dict(test,testPassed=passed);tests.append(test)
  support=group['signatureInterface']=='internal' or group.get('preHash')=='pure'
  inventory.append(dict(group=group['tgId'],case=test['tcId'],interface=group['signatureInterface'],prehash=group.get('preHash','not applicable'),message_bytes=len(test['message'])//2,context_bytes=len(test.get('context',''))//2,signature_bytes=len(test['signature'])//2,expected=passed,reference_scope='supported' if support else 'preHash interface outside pure baseline'))
  if support:
   context=bytes.fromhex(test.get('context',''))
   framed=bytes.fromhex(test['message'])
   if group['signatureInterface']=='external':framed=bytes([0,len(context)])+context+framed
   supported.append((test,group,framed))
 groups.append(dict(group,tests=tests))
assert len(groups)==3 and len(inventory)==42 and len(supported)==28
selected=dict(algorithm=prompt['algorithm'],mode=prompt['mode'],revision=prompt['revision'],parameterSet='SLH-DSA-SHA2-128s',upstream_prompt_sha256=hashlib.sha256(raw).hexdigest(),source_revision='975de31eb83d87039ec88934fdc47d8c312b892d',testGroups=groups)
(OUT/'acvp-sha2-128s.json').write_text(json.dumps(selected,indent=2)+'\n')
with (OUT/'acvp-inventory.tsv').open('w',newline='') as f:
 writer=csv.DictWriter(f,list(inventory[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(inventory)
with (OUT/'acvp-supported.tsv').open('w',newline='') as f:
 writer=csv.writer(f,delimiter='\t',lineterminator='\n');writer.writerow(['group','case','publickey','framedmessage','signature','expected'])
 for test,group,framed in supported:
  writer.writerow([group['tgId'],test['tcId'],test['pk'],framed.hex(),test['signature'],str(test['testPassed']).lower()])
# Deterministic minimal framed-message valid fixture, not a purported full KAT run.
test,group,framed=min((r for r in supported if r[0]['testPassed']),key=lambda r:(len(r[2]),r[0]['tcId']))
rows={'group':str(group['tgId']),'case':str(test['tcId']),'interface':group['signatureInterface'],'publickey':test['pk'],'framedmessage':framed.hex(),'signature':test['signature'],'expected':'true'}
(OUT/'acvp-selected-kat.txt').write_text(''.join(k+'='+v+'\n' for k,v in rows.items()))
print(json.dumps(dict(selected_groups=len(groups),all_cases=len(inventory),supported_reference_cases=len(supported),prehash_deferred=14,selected_simplicity_case=test['tcId'],framed_message_bytes=len(framed),source_prompt_sha256=selected['upstream_prompt_sha256']),indent=2))
