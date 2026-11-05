#!/usr/bin/env python3
"""Extract the complete original two-transaction block; inventory all Core tests."""
from pathlib import Path
import hashlib,json,re,csv
root=Path(__file__).resolve().parents[1];p=root/'vendor-specs/bitcoin-growth5'
raw=(root/'vendor-specs/spv/mainnet-170.block').read_bytes()
def compact(pos):
 b=raw[pos];pos+=1
 if b<253:return b,pos
 size={253:2,254:4,255:8}[b];return int.from_bytes(raw[pos:pos+size],'little'),pos+size
def transaction(pos):
 begin=pos;pos+=4;ni,pos=compact(pos);assert ni>0
 for _ in range(ni):pos+=36;n,pos=compact(pos);pos+=n+4
 no,pos=compact(pos)
 for _ in range(no):pos+=8;n,pos=compact(pos);pos+=n
 return raw[begin:pos+4],pos+4
n,pos=compact(80);assert n==2
cb,pos=transaction(pos);tx,pos=transaction(pos);assert pos==len(raw)
hash2=lambda d:hashlib.sha256(hashlib.sha256(d).digest()).digest()
assert hash2(hash2(cb)+hash2(tx))==raw[36:68]
metadata=json.loads((root/'vendor-specs/spv/mainnet-170.json').read_text())
assert hash2(raw[:80])[::-1].hex()==metadata['id']
fields={'header_raw':raw[:80].hex(),'block_hash_raw':hash2(raw[:80]).hex(),'block_hash_display':metadata['id'],'coinbase_raw':cb.hex(),'transaction_raw':tx.hex(),'coinbase_txid_raw':hash2(cb).hex(),'transaction_txid_raw':hash2(tx).hex(),'merkle_root_raw':raw[36:68].hex(),'compact_nonce':'81985529216486895'}
(p/'bip152-historical-fixture.tsv').write_text('field\tvalue\n'+''.join(f'{k}\t{v}\n'for k,v in fields.items()))
s=(p/'core-src_test_blockencodings_tests.cpp.txt').read_text();cases=list(re.finditer(r'BOOST_AUTO_TEST_CASE\(([^)]+)\)',s))
assert len(cases)==8
with(p/'core-bip152-test-inventory.tsv').open('w',newline='')as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['case','source_line','published_form','coverage'])
 for case in cases:
  name=case[1];line=s[:case.start()].count('\n')+1
  coverage='independent reference reproduces complete differential-index example/bounds; not executing upstream C++'if name.startswith('TransactionsRequest')else('bounded two-transaction analogue only; original three-transaction randomized procedure outside exact native bound'if name=='SimpleRoundTripTest'else'outside bounded two-transaction/coinbase-prefill/one-candidate client; retained source procedure not executed')
  w.writerow([name,line,'C++ test procedure, not a published static block/shortID JSON vector',coverage])
print(f'PASS all{len(cases)} official Core procedures inventoried; complete real block170 parsed, tx sizes{len(cb)}/{len(tx)} and exact Merkle/header hashes verified')
