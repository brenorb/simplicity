#!/usr/bin/env python3
"""Pinned documentary inputs for four approved, separately counted families.

Rust/C/Sage files are read only as specification/constants/KAT data; this
downloader never compiles, executes, imports or evaluates any downloaded code.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime,hashlib,json,subprocess,zipfile
ROOT=Path(__file__).resolve().parents[1]
DEST=ROOT/'vendor-specs/crypto-families'
REVS={
 'BLAKE3-team/BLAKE3':'f55849f89cd85083c1c9daa2c5de20766f309c00',
 'BLAKE3-team/BLAKE3-specs':'ac784c9f22a48327782f042ec2f4d8126b3b1744',
 'BitVM/BitVM':'c620dbfaacebdf778e765a6681985350389973b1',
 'HorizenLabs/poseidon2':'055bde3f4782731ba5f5ce5888a440a94327eaf3',
 'GOATNetwork/bitvm-gc':'a4dab03c56515ad4882dd73fd78c76edbe9dcc56',
 'ProjectZKM/poseidon2':'f98a6048c370d97f1de3320f8136d379f63fa8bd',
 'ProjectZKM/Ziren':'f10a9b4b0039b655b9e3588fa2f79157f5dbda8c',
 'Plonky3/Plonky3':'v0.5.1'}
SOURCES=[]
def repo(repo,path,name,license_note):
 rev=REVS[repo];SOURCES.append((name,f'https://raw.githubusercontent.com/{repo}/{rev}/{path}',rev,license_note))
for path in ['test_vectors/test_vectors.json','LICENSE_A2','LICENSE_A2LLVM','LICENSE_CC0','reference_impl/reference_impl.rs']:
 repo('BLAKE3-team/BLAKE3',path,'blake3-'+path.replace('/','_'),'Official repository license texts fetched separately; source files data only.')
repo('BLAKE3-team/BLAKE3-specs','blake3.pdf','blake3-spec.pdf','Authors specification; notice retained; repository revision pinned.')
repo('BitVM/BitVM','README.md','bitvm-README.md','MIT license text fetched separately.')
repo('BitVM/BitVM','LICENSE','bitvm-LICENSE','Verbatim source license.')
repo('BitVM/BitVM','bitvm/src/hash/blake3.rs','bitvm-blake3.rs.txt','MIT; source data only, not executed.')
repo('BitVM/BitVM','bitvm/src/chunk/wrap_hasher.rs','bitvm-wrap_hasher.rs.txt','MIT; direct chunk commitment hash callsite, source data only.')
for path in ['README.md','LICENSE-APACHE','LICENSE-MIT','plain_implementations/src/poseidon2/poseidon2.rs','plain_implementations/src/poseidon2/poseidon2_params.rs','plain_implementations/src/poseidon2/poseidon2_instance_bn256.rs']:
 repo('HorizenLabs/poseidon2',path,'poseidon2-'+path.replace('/','_'),'Apache2.0 OR MIT; full notices fetched; source/constants/KATs are data only.')
repo('HorizenLabs/poseidon2','plain_implementations/src/fields/bn256.rs','poseidon2-bn256-field.rs.txt','Apache2.0 OR MIT; field modulus source data.')
for path in ['Cargo.toml','Cargo.lock']:
 repo('GOATNetwork/bitvm-gc',path,'bitvm-gc-root-'+path,'Repository license unspecified; exact dependency provenance data.')
for path in ['README.md','garbled-snark-verifier/Cargo.toml','garbled-snark-verifier/src/dv_bn254/dv_ref.rs','garbled-snark-verifier/src/dv_bn254/dv_snark.rs','garbled-snark-verifier/src/circuits/sect233k1/dv_ref.rs','garbled-snark-verifier/src/circuits/sect233k1/dv_ckt.rs']:
 repo('GOATNetwork/bitvm-gc',path,'bitvm-gc-'+path.replace('/','_'),'No blanket license inferred; file notices retained and repository license inventory recorded separately. Data only.')
for path in ['verifiable-circuit/src/main.rs','verifiable-circuit/Cargo.toml']:
 repo('GOATNetwork/bitvm-gc',path,'bitvm-gc-'+path.replace('/','_'),'No blanket license inferred; direct application callsite/dependency source data only.')
for path in ['garbled-snark-verifier/src/core/wire.rs','garbled-snark-verifier/src/core/gate.rs','garbled-snark-verifier/src/core/s.rs','garbled-snark-verifier/src/core/utils.rs']:
 repo('GOATNetwork/bitvm-gc',path,'bitvm-gc-'+path.replace('/','_'),'No blanket license inferred; actual garbling hash callsite source data only.')
for path in ['src/lib.rs','src/permute.rs','Cargo.toml']:
 repo('ProjectZKM/poseidon2',path,'zkm-poseidon2-'+path.replace('/','_'),'No blanket license inferred; constants/wrapper source read only as data.')
for path in ['crates/primitives/src/lib.rs','crates/test-artifacts/guests/poseidon2-permute/src/main.rs','LICENSE-APACHE','LICENSE-MIT']:
 repo('ProjectZKM/Ziren',path,'ziren-'+path.replace('/','_'),'Repository license texts fetched separately if present; source data only.')
for path in ['koala-bear/src/poseidon2.rs','poseidon2/src/external.rs','monty-31/src/poseidon2.rs','koala-bear/src/koala_bear.rs','LICENSE-APACHE','LICENSE-MIT']:
 repo('Plonky3/Plonky3',path,'plonky3-'+path.replace('/','_'),'Apache2.0 OR MIT; published version tagv0.5.1 plus exact SHA256 pins bytes. GitHub tag API403 was not substituted with a guessed commit.')
SOURCES +=[
 ('fips202.pdf','https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf','FIPS202 August2015','Official NIST publication; no additional license inferred.'),
 ('shakebytetestvectors.zip','https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/shakebytetestvectors.zip','Official NIST CAVP byte-oriented SHAKE vectors; byte hash pins snapshot','Source README/notices retained; informal test vectors are not CAVP validation.')]
def fetch(row):
 name,url,rev,license_note=row;p=DEST/name;tmp=p.with_name(name+'.partial')
 r=subprocess.run(['curl','--fail','--silent','--show-error','--location','--max-time','60',url,'--output',str(tmp)],capture_output=True,text=True)
 out=dict(file=name,url=url,revision=rev,license_note=license_note,curl_exit_status=r.returncode)
 if r.returncode:out['access_gap']=r.stderr.strip();tmp.unlink(missing_ok=True)
 else:
  b=tmp.read_bytes()
  if name.endswith('.pdf') and not b.startswith(b'%PDF-'):
   out['access_gap']='HTTP response is not the requested PDF';tmp.unlink()
  else:tmp.replace(p);out.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
 return out
def main():
 DEST.mkdir(parents=True,exist_ok=True)
 with ThreadPoolExecutor(max_workers=4) as pool:rows=list(pool.map(fetch,SOURCES))
 meta={'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'external_code_executed':False,'sources':rows}
 (DEST/'manifest.json').write_text(json.dumps(meta,indent=2)+'\n')
 for r in rows:print(r['file'],r.get('access_gap','OK'))
 z=DEST/'shakebytetestvectors.zip'
 if z.exists():
  with zipfile.ZipFile(z) as archive:
   names=archive.namelist();(DEST/'shake-zip-inventory.json').write_text(json.dumps(names,indent=2)+'\n')
   for name in names:
    leaf=Path(name).name
    if leaf in ['SHAKE256ShortMsg.rsp','SHAKE256LongMsg.rsp','SHAKE256VariableOut.rsp','README.txt','Readme.txt']:
     info=archive.getinfo(name)
     assert info.file_size<10_000_000
     data=archive.read(name);(DEST/leaf).write_bytes(data)
if __name__=='__main__':main()
