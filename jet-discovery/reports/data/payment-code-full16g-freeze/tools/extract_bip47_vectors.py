#!/usr/bin/env python3
"""Extract every BIP47-linked v1 vector; derive HD data with stdlib only."""
from pathlib import Path
import re,hashlib,hmac,csv,json
root=Path(__file__).resolve().parents[1];source=root/'vendor-specs/bitcoin-growth7/bip47-vectors-gist.md';s=source.read_text();p=root/'vendor-specs/bitcoin-growth8';p.mkdir(exist_ok=True)
alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
hash2=lambda b:hashlib.sha256(hashlib.sha256(b).digest()).digest()
def base58(encoded):
 value=0
 for c in encoded:value=value*58+alphabet.index(c)
 raw=b'\0'*(len(encoded)-len(encoded.lstrip('1')))+value.to_bytes((value.bit_length()+7)//8,'big');assert hash2(raw[:-4])[:4]==raw[-4:];return raw[:-4]
def label(name):
 m=re.search(r'\*\*'+re.escape(name)+r':\*\* ([^\n]+)',s);assert m,name;return m[1]
def scalar(name):
 m=re.search(r'\*'+re.escape(name)+r'\*: ([0-9a-f]+)',s);assert m,name;return bytes.fromhex(m[1])
codes=re.findall(r'^PM[1-9A-HJ-NP-Za-km-z]+$',s,re.M);assert len(codes)==2
payloads=[base58(c)for c in codes];assert all(len(b)==81 and b[:3]==bytes.fromhex('470100')and b[3]in(2,3)and b[68:]==b'\0'*13 for b in payloads)
seeds=[bytes.fromhex(x)for x in re.findall(r'\*\*BIP32 seed hex:\*\* ([0-9a-f]+)',s)];assert len(seeds)==2
accounts=[]
for name,seed,payload in zip(['alice','bob'],seeds,payloads):
 digest=hmac.digest(b'Bitcoin seed',seed,'sha512');key=int.from_bytes(digest[:32],'big');chain=digest[32:]
 for i in [47+2**31,2**31,2**31]:
  digest=hmac.digest(chain,b'\0'+key.to_bytes(32,'big')+i.to_bytes(4,'big'),'sha512');assert int.from_bytes(digest[:32],'big')<n;key=(key+int.from_bytes(digest[:32],'big'))%n;assert key>0;chain=digest[32:]
 code=payload[1:];assert chain==code[35:67]
 accounts.append(dict(name=name,payload=code.hex(),public=code[2:35].hex(),chain=chain.hex(),private=f'{key:064x}'))
alice,bob=accounts;pay_address_section=s.split('###The first 10 addresses')[1].split('###Alice\'s notification')[0]
addresses=re.findall(r'^1[1-9A-HJ-NP-Za-km-z]+$',pay_address_section,re.M);assert len(addresses)==10
payments=[]
for i,address in enumerate(addresses):
 private=scalar('b'+str(i));public=scalar('B'+str(i));shared=scalar('S'+str(i));assert len(private)==32 and len(public)==33 and len(shared)==32
 digest=hmac.digest(bytes.fromhex(bob['chain']),bytes.fromhex(bob['public'])+i.to_bytes(4,'big'),'sha512')
 assert (int.from_bytes(digest[:32],'big')+int(bob['private'],16))%n==int.from_bytes(private,'big')
 address_payload=base58(address);assert len(address_payload)==21 and address_payload[0]==0
 payments.append(dict(index=i,private=private.hex(),public=public.hex(),shared_x=shared.hex(),address=address,pubkey_hash=address_payload[1:].hex(),IL=digest[:32].hex(),IR=digest[32:].hex(),derived_tweak_sha256=hashlib.sha256(shared).hexdigest()))
a0=scalar('a0');A0=scalar('A0');digest=hmac.digest(bytes.fromhex(alice['chain']),bytes.fromhex(alice['public'])+b'\0'*4,'sha512')
assert(int.from_bytes(digest[:32],'big')+int(alice['private'],16))%n==int.from_bytes(a0,'big')
raw=bytes.fromhex(label('Notification transaction to be pushed'));display=label('Notification transaction hash');assert hash2(raw)[::-1].hex()==display
outpoint=bytes.fromhex(label('Outpoint of first UTXO in Alice\'s notification transaction to Bob'));assert raw[5:41]==outpoint
plain=bytes.fromhex(label('Alice\'s payment code payload'));blinded=bytes.fromhex(label('Alice\'s payment code payload after blinding'));mask=bytes.fromhex(label('Blinding mask'));ecdh=bytes.fromhex(label('Shared secret'))
assert plain==bytes.fromhex(alice['payload'])and len(mask)==64 and hmac.digest(outpoint,ecdh,'sha512')==mask
rebuilt=plain[:3]+bytes(a^b for a,b in zip(plain[3:67],mask))+plain[67:];assert rebuilt==blinded and raw[-84:-4]==blinded
wif=base58(label('private key of input unassociated with Alice\'s payment code'));assert len(wif)==34 and wif[0]==128 and wif[-1]==1
fixture=dict(notification_raw=raw.hex(),notification_txid_raw=hash2(raw).hex(),notification_txid_display=display,outpoint_raw=outpoint.hex(),designated_input_private=wif[1:-1].hex(),ecdh_x=ecdh.hex(),mask=mask.hex(),plain_payload=plain.hex(),blinded_payload=blinded.hex(),alice_a0=a0.hex(),alice_A0=A0.hex(),alice_child0_IL=digest[:32].hex(),alice_child0_IR=digest[32:].hex(),bob_b0=payments[0]['private'],bob_B0=payments[0]['public'])
for name,rows in [('bip47-accounts.tsv',accounts),('bip47-all-payments.tsv',payments)]:
 with(p/name).open('w',newline='')as f:w=csv.DictWriter(f,rows[0],delimiter='\t',lineterminator='\n');w.writeheader();w.writerows(rows)
(p/'bip47-notification-fixture.tsv').write_text('field\tvalue\n'+''.join(f'{k}\t{v}\n'for k,v in fixture.items()))
(p/'coverage.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'primary_vector_revision':'beddb67cf219ead27b8b1380a3b084b8dde51093','accounts':2,'published_child_pairs':11,'published_ecdh_x_and_address_cases':10,'complete_signed_notification_cases':1,'source_scope':'v1/noBitmessage, source full set; mnemonics/entropy are setup metadata, not claimed native BIP39PBKDF work; actual ECDH/points/addresses/signature checked by local Haskell reference separately','native_application_status':'not yet implemented/credited'},indent=2)+'\n')
print('PASS full BIP47 vector extraction:2accounts/11published childpairs/10addresses+ECDH-x/1complete notification; stdlib HD+mask/wirechecks')
