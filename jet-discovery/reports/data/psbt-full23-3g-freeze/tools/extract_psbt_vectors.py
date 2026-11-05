#!/usr/bin/env python3
"""Inventory every inline BIP174/370 binary vector; never execute source code."""
from pathlib import Path
import base64,csv,hashlib,json,re
root=Path(__file__).resolve().parents[1];out=root/'vendor-specs/bitcoin-growth9';out.mkdir(exist_ok=True)
class Reader:
 def __init__(self,b):self.b=b;self.p=0
 def read(self,n):
  if n<0 or self.p+n>len(self.b):raise ValueError('truncated bytes')
  x=self.b[self.p:self.p+n];self.p+=n;return x
 def compact(self):
  x=self.read(1)[0]
  if x<253:return x
  n={253:2,254:4,255:8}[x];v=int.from_bytes(self.read(n),'little')
  if v<{253:253,254:65536,255:2**32}[x]:raise ValueError('nonminimal CompactSize')
  return v
 def string(self):return self.read(self.compact())
 def end(self):
  if self.p!=len(self.b):raise ValueError('trailing bytes')
def psbtmap(r):
 m={}
 while True:
  key=r.string()
  if not key:return m
  kr=Reader(key);kr.compact()
  if key in m:raise ValueError('duplicate map key')
  m[key]=r.string()
def tx(raw,unsigned=False):
 r=Reader(raw);version=r.read(4);n=r.compact();segwit=False
 if not unsigned and n==0 and r.p<len(raw) and raw[r.p]==1:
  r.read(1);segwit=True;n=r.compact()
 ins=[]
 for i in range(n):
  h=r.read(32);j=r.read(4);s=r.string();seq=r.read(4)
  if unsigned and s:raise ValueError('nonempty unsigned input scriptSig')
  ins.append((h,j,s,seq))
 outputs=[(r.read(8),r.string())for i in range(r.compact())]
 witnesses=[[r.string()for j in range(r.compact())]for i in ins]if segwit else []
 lock=r.read(4);r.end();return version,ins,outputs,witnesses,lock
def onecompact(b):
 r=Reader(b);v=r.compact();r.end();return v
def parse(raw):
 r=Reader(raw)
 if r.read(5)!=bytes.fromhex('70736274ff'):raise ValueError('PSBT magic')
 glob=psbtmap(r);version=int.from_bytes(glob.get(b'\xfb',b'\0'*4),'little')
 if version==0:
  if b'\x00'not in glob:raise ValueError('missing unsigned transaction')
  _,ins,outs,_,_=tx(glob[b'\x00'],True);ni,no=len(ins),len(outs)
 elif version==2:
  if any(k not in glob for k in [b'\x02',b'\x04',b'\x05']):raise ValueError('missing v2 global field')
  ni,no=onecompact(glob[b'\x04']),onecompact(glob[b'\x05'])
 else:raise ValueError('unsupported PSBT version')
 inputs=[psbtmap(r)for i in range(ni)];outputs=[psbtmap(r)for i in range(no)];r.end()
 return version,glob,inputs,outputs
def inspect(raw):
 try:
  version,g,ins,outs=parse(raw)
  return dict(map_parse='ok',version=version,inputs=len(ins),outputs=len(outs),global_keys=','.join(k.hex()for k in g),input_keys=';'.join(','.join(k.hex()for k in m)for m in ins),output_keys=';'.join(','.join(k.hex()for k in m)for m in outs))
 except ValueError as e:return dict(map_parse=str(e),version='',inputs='',outputs='',global_keys='',input_keys='',output_keys='')
def locktime(raw):
 version,g,inputs,_=parse(raw);assert version==2
 def word(b):assert len(b)==4;return int.from_bytes(b,'little')
 constrained=[m for m in inputs if b'\x11'in m or b'\x12'in m]
 if not constrained:return word(g.get(b'\x03',b'\0'*4))
 for key in (b'\x12',b'\x11'): # BIP370 chooses height when both types fit.
  if all(key in m for m in constrained):return max(word(m[key])for m in constrained)
 return 'incompatible'
rows=[];sources=[]
for number in ['0174','0370']:
 source=root/f'vendor-specs/bitcoin-growth3/bip-{number}.mediawiki';text=source.read_text();sources.append(dict(path=str(source.relative_to(root)),sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
 category='outside-test-section';case='';expected='';counter=0;pending=None;last_case=None
 for line_no,line in enumerate(text.splitlines(),1):
  if line.startswith('==Test Vectors=='):category='workflow';case='unlabelled workflow vector'
  if line.startswith('The following are invalid PSBTs'):category='invalid';expected='invalid PSBT'
  elif line.startswith('The following are valid PSBTs'):category='valid';expected='valid PSBT'
  elif 'The following tests are the timelock determination algorithm' in line:category='locktime'
  elif 'The timelock for the following PSBTs' in line:
   expected='incompatible'if'cannot be computed'in line else re.search(r'to be ([0-9]+)',line)[1]
  elif number=='0174'and line=='Fails Signer checks':category='role-invalid';expected='invalid signer data'
  elif number=='0174'and line.startswith('The private keys in the tests below'):
   category='workflow';expected='published role transition';case='workflow: creator/updater/signer/combiner/finalizer/extractor'
  if line.startswith('* Case:'):case=line.split(':',1)[1].strip()
  m=re.search(r'Bytes in Hex: <pre>([0-9a-fA-F]+)</pre>',line,re.I)
  if m:
   counter+=1;raw=bytes.fromhex(m[1]);record=dict(source=number,ordinal=counter,line=line_no,category=category,case=case,expected=expected,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),hex=raw.hex(),base64_matches='missing')
   if number=='0174'and counter==42:record.update(case='workflow: extracted network transaction',expected='published extracted network bytes')
   if category=='locktime'and case==last_case:record['case']='Second unlabelled wire record in the same expected locktime group'
   record['locktime_reference']=''
   if category=='locktime':record['locktime_reference']=str(locktime(raw));assert record['locktime_reference']==expected
   record['native_scope']='exact published finalizer relation'if number=='0174'and counter in(40,41,42)else'outside exact native session; inventoried source evidence'
   record.update(inspect(raw));rows.append(record);pending=record
   last_case=case
  b64=re.search(r'Base64 String: <pre>([^<]+)</pre>',line)
  if b64:
   if pending is None:raise ValueError('Base64 without a preceding hex vector')
   pending['base64_matches']=str(base64.b64decode(b64[1],validate=True).hex()==pending['hex']).lower()
   if pending['base64_matches']!='true':raise ValueError('source Hex/Base64 mismatch')
   pending=None
with(out/'psbt-all-inline-vectors.tsv').open('w',newline='')as f:
 w=csv.DictWriter(f,rows[0],delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
coverage=dict(sources=sources,total_binary_vectors=len(rows),by_source={n:sum(r['source']==n for r in rows)for n in ['0174','0370']},base64_pairs=sum(r['base64_matches']=='true'for r in rows),all_bip370_locktime_reference_cases=sum(r['locktime_reference']!=''for r in rows),map_parser_scope='minimal CompactSize, map key uniqueness/framing, version/count reconstruction and blank unsigned scriptSig only; NOT full field/UTXO/signature/role validation',native_application_status='source extraction alone earns no count credit; actual bounded verifier evidence separate')
(out/'coverage.json').write_text(json.dumps(coverage,indent=2)+'\n')
source=(root/'vendor-specs/bitcoin-growth3/bip-0174.mediawiki').read_text()
alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def base58check(encoded):
 value=0
 for character in encoded:value=value*58+alphabet.index(character)
 raw=b'\0'*(len(encoded)-len(encoded.lstrip('1')))+value.to_bytes((value.bit_length()+7)//8,'big')
 assert hashlib.sha256(hashlib.sha256(raw[:-4]).digest()).digest()[:4]==raw[-4:]
 return raw[:-4]
signers={}
for encoded,index in re.findall(r"\* <tt>(c[1-9A-HJ-NP-Za-km-z]+)</tt> \(<tt>m/0'/0'/([0-3])'</tt>\)",source):
 raw=base58check(encoded);assert len(raw)==34 and raw[0]==0xef and raw[-1]==1 and index not in signers
 signers[index]=raw[1:-1].hex()
assert set(signers)==set('0123')
(out/'psbt-published-signer-private-fixtures.tsv').write_text('source_child\tpublic_test_private32\n'+''.join(f'{i}\t{signers[i]}\n'for i in sorted(signers)))
print(json.dumps(coverage,indent=2))
for r in rows:
 if r['map_parse']=='ok'and r['category']=='valid':print(r['source'],r['ordinal'],r['case'],r['inputs'],r['outputs'],r['input_keys'])
