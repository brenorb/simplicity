#!/usr/bin/env python3
"""Complete pinned BIP32 extended-key inventory and independent stdlib HMACs."""
from pathlib import Path
import re,hashlib,hmac,csv,json
root=Path(__file__).resolve().parents[1];p=root/'vendor-specs/bitcoin-growth6';p.mkdir(exist_ok=True)
spec=root/'vendor-specs/bitcoin-growth3/bip-0032.mediawiki';text=spec.read_text()
alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';order=0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141;prime=2**256-2**32-977
hash2=lambda x:hashlib.sha256(hashlib.sha256(x).digest()).digest()
def decode(s):
 try:
  n=0
  for c in s:n=n*58+alphabet.index(c)
  raw=b'\0'*(len(s)-len(s.lstrip('1')))+n.to_bytes((n.bit_length()+7)//8,'big')
  if len(raw)!=82 or hash2(raw[:-4])[:4]!=raw[-4:]:return None
  b=raw[:-4];version=int.from_bytes(b[:4],'big');depth=b[4];finger=b[5:9];index=int.from_bytes(b[9:13],'big');chain=b[13:45];key=b[45:]
  if depth==0 and(finger!=b'\0'*4 or index!=0):return None
  if version==0x0488ade4:
   if key[0]!=0 or not 0<int.from_bytes(key[1:],'big')<order:return None
   kind='private'
  elif version==0x0488b21e:
   x=int.from_bytes(key[1:],'big');rhs=(x**3+7)%prime
   if key[0]not in(2,3)or x>=prime or pow(rhs,(prime-1)//2,prime)!=1:return None
   kind='public'
  else:return None
  return dict(kind=kind,depth=depth,fingerprint=finger,index=index,chain=chain,key=key)
 except(ValueError,OverflowError):return None
sections=re.split(r'===Test vector (\d)===',text)[1:];valid=[];invalid=[];public=[];edges=[]
for number,section in zip(sections[::2],sections[1::2]):
 if number=='5':
  for encoded,note in re.findall(r'^\* (\S+) \(([^\n]+)\)',section,re.M):
   assert decode(encoded)is None,(encoded,note);invalid.append(dict(vector=number,key=encoded,note=note,verdict='reject'))
  continue
 seed=bytes.fromhex(re.search(r'Seed \(hex\): (\w+)',section)[1]);seen={}
 for path,xpub,xprv in re.findall(r'\* Chain ([^\n]+)\n\*\* ext pub: (\S+)\n\*\* ext prv: (\S+)',section):
  path=path.replace('<sub>H</sub>',"'");a=decode(xpub);b=decode(xprv);assert a and b and a['kind']=='public'and b['kind']=='private'
  assert all(a[k]==b[k]for k in ['depth','fingerprint','index','chain'])
  if path=='m':
   digest=hmac.digest(b'Bitcoin seed',seed,'sha512');assert digest[:32]==b['key'][1:]and digest[32:]==b['chain']
  else:
   parent_path,last=path.rsplit('/',1);pa,pb=seen[parent_path];index=int(last.rstrip("'"))+(2**31 if last.endswith("'")else 0)
   data=(pb['key']if index>=2**31 else pa['key'])+index.to_bytes(4,'big');digest=hmac.digest(pa['chain'],data,'sha512')
   assert int.from_bytes(b['key'][1:],'big')==(int.from_bytes(digest[:32],'big')+int.from_bytes(pb['key'][1:],'big'))%order
   assert b['chain']==digest[32:]and b['index']==index and b['depth']==pa['depth']+1
   assert b['fingerprint']==hashlib.new('ripemd160',hashlib.sha256(pa['key']).digest()).digest()[:4]
   row=dict(vector=number,path=path,parent_public=pa['key'].hex(),parent_chain=pa['chain'].hex(),index=index,IL=digest[:32].hex(),IR=digest[32:].hex(),child_public=a['key'].hex(),child_chain=a['chain'].hex(),parent_private=pb['key'][1:].hex(),child_private=b['key'][1:].hex())
   edges.append(row)
   if index<2**31:public.append(row)
  seen[path]=(a,b);valid.append(dict(vector=number,path=path,public_extended=xpub,private_extended=xprv,public=a['key'].hex(),private=b['key'][1:].hex(),chain=a['chain'].hex(),depth=a['depth'],index=a['index']))
assert len(valid)==17 and len(invalid)==16 and len(edges)==13 and len(public)==6,(len(valid),len(invalid),len(edges),len(public))
for name,rows in [('bip32-all-valid.tsv',valid),('bip32-all-invalid.tsv',invalid),('bip32-all-ckd-edges.tsv',edges),('bip32-public-ckd-vectors.tsv',public)]:
 with(p/name).open('w',newline='')as f:
  w=csv.DictWriter(f,rows[0],delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
master=next(r for r in valid if r['vector']=='2' and r['path']=='m')
wallet=[]
for index in [0,1,2147483647,2147483648]:
 digest=hmac.digest(bytes.fromhex(master['chain']),bytes.fromhex(master['public'])+index.to_bytes(4,'big'),'sha512')
 secret=(int.from_bytes(digest[:32],'big')+int(master['private'],16))%order
 wallet.append(dict(index=index,parent_public=master['public'],parent_chain=master['chain'],parent_private=master['private'],IL=digest[:32].hex(),IR=digest[32:].hex(),child_private=f'{secret:064x}',decision='valid nonhardened public CKD'if index<2**31 else'public formula only: forbidden hardened index; must reject'))
with(p/'bip32-wallet-derived.tsv').open('w',newline='')as f:
 w=csv.DictWriter(f,wallet[0],delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(wallet)
(p/'manifest.json').write_text(json.dumps({'kind':'Local literal extraction and independent Python stdlib HMAC-SHA512 from full pinned BIP32 text','primary_source':'../bitcoin-growth3/bip-0032.mediawiki','primary_sha256':hashlib.sha256(spec.read_bytes()).hexdigest(),'source_url':'https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0032.mediawiki','revision':'a0c977f3755da6476b955677ca9318334a2432c4','license':'BSD-2-Clause per retained BIP32','coverage':'All5 sections:17 valid extended-key pairs/34keys,16invalidkeys,4master seeds,13private CKD edges and all6public CKD edges; native wallet/core validation remains separate','records':[{'file':f.name,'bytes':f.stat().st_size,'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}for f in sorted(p.glob('*.tsv'))]},indent=2)+'\n')
print('PASS all5BIP32sections/50extendedkeys;4master seeds/13CKD edges independently reconstructed;6public CKD cores extracted')
