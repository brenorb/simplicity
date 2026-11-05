#!/usr/bin/env python3
"""Read fixed Rust arrays as DATA; never evaluate/compile imported Rust/Sage."""
from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'vendor-specs/crypto-families'
manifest=json.loads((DATA/'manifest.json').read_text())
for name in ['plonky3-koala-bear_src_poseidon2.rs','ziren-crates_primitives_src_lib.rs']:
 row=next(r for r in manifest['sources'] if r['file']==name)
 assert hashlib.sha256((DATA/name).read_bytes()).hexdigest()==row['sha256']
p=(DATA/'plonky3-koala-bear_src_poseidon2.rs').read_text()
z=(DATA/'ziren-crates_primitives_src_lib.rs').read_text()
def array(name,kind,count):
 m=re.search(name+r'.*?=\s*KoalaBear::'+kind+r'\(\[(.*?)\]\);',p,re.S)
 assert m,name
 values=[int(x,0) for x in re.findall(r'0x[0-9a-fA-F]+|\b\d+\b',m[1])]
 assert len(values)==count,(name,len(values));return values
initial=array('KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL','new_2d_array',64)
final=array('KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL','new_2d_array',64)
internal=array('KOALABEAR_POSEIDON2_RC_16_INTERNAL','new_array',20)
block=z.split('pub static ref RC_16_30:',1)[1].split('=',1)[1].split('];',1)[0]
raw=[int(x) for x in re.findall(r'KoalaBear::from_u32\((\d+)\)',block)]
assert len(raw)==480
q=2130706433
raw=[x%q for x in raw]
kat=p.split('fn test_default_koalabear_poseidon2_width_16()',1)[1].split('#[test]',1)[0]
def kat_array(name):
 m=re.search(name+r':.*?KoalaBear::new_array\(\[(.*?)\]\);',kat,re.S);assert m
 out=[int(x) for x in re.findall(r'\b\d+\b',m[1])];assert len(out)==16;return out
ki,ko=kat_array('input'),kat_array('expected')
rows=lambda a:[a[i:i+16] for i in range(0,len(a),16)]
payload={'field_modulus':q,'width':16,'sbox_degree':3,'full_rounds':8,'partial_rounds':20,
 'default':{'initial':rows(initial),'internal':internal,'final':rows(final)},
 'ziren':{'initial':rows(raw[:64]),'internal':[raw[16*i] for i in range(4,24)],'final':rows(raw[384:448])},
 'published_default_kat':{'input':ki,'expected':ko},
 'ziren_note':'Exact poseidon2_init consumes first28of30 rows; last2rows unused. No published expected-output KAT found for these exact constants.'}
(DATA/'poseidon2-extracted.json').write_text(json.dumps(payload,indent=2)+'\n')
out=['-- Generated from fixed data arrays by tools/extract_poseidon2_data.py.',
 '-- Primary sources/license texts and exact hashes: vendor-specs/crypto-families/.',
 '-- Plonky3 and Ziren are Apache-2.0 OR MIT. No downloaded code is executed.',
 'module JetDiscovery.Ref.Poseidon2Constants where','']
for prefix,obj in [('default',payload['default']),('ziren',payload['ziren'])]:
 for name,values in obj.items():
  typ='[Integer]' if name=='internal' else '[[Integer]]'
  out +=[prefix+name.title()+' :: '+typ,prefix+name.title()+' = '+repr(values),'']
for name,values in [('katInput',ki),('katExpected',ko)]:out+=[name+' :: [Integer]',name+' = '+repr(values),'']
(ROOT/'src/JetDiscovery/Ref/Poseidon2Constants.hs').write_text('\n'.join(out))
print('Extracted two exact parameter profiles and the full16-field published default KAT; one counting family.')
