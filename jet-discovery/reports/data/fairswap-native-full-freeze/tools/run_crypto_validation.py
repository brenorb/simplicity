#!/usr/bin/env python3
"""Freeze local sources/binary, then run an explicitly sequential vector batch."""
from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess,time
ROOT=Path(__file__).resolve().parents[1]
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
p=argparse.ArgumentParser()
p.add_argument('--label',required=True);p.add_argument('--binary',type=Path,required=True)
p.add_argument('--build-dir',type=Path,required=True);p.add_argument('--driver',type=Path,required=True)
p.add_argument('--heap',type=int,required=True);p.add_argument('--group',action='append',required=True)
p.add_argument('--compiler-flags',default='-O1 -threaded -rtsopts')
a=p.parse_args();assert a.heap>0 and a.label.replace('-','').isalnum()
data=ROOT/'reports/data';freeze=data/(a.label+'-full-freeze')
assert not freeze.exists() and not(data/(a.label+'-full-provenance.json')).exists(), 'use a fresh label; validation evidence is immutable'
freeze.mkdir()
sources=[]
for hi in sorted(a.build_dir.rglob('*.hi')):
 rel=hi.relative_to(a.build_dir).with_suffix('.hs');src=ROOT/'src'/rel
 if src.is_file():sources.append(src)
sources.append((ROOT/a.driver).resolve())
sources.append(Path(__file__).resolve())
records=[]
for src in sorted(set(sources)):
 rel=src.relative_to(ROOT);dest=freeze/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
 records.append(dict(path=str(rel),sha256=sha(src),frozen_path=str(dest.relative_to(ROOT))))
runtime_data=[]
for rel in ['vendor-specs/crypto-families/blake3-unkeyed-bounded.tsv','vendor-specs/crypto-families/shake256-kat250.tsv','vendor-specs/crypto-families/poseidon2-extracted.json','vendor-specs/crypto-families/manifest.json']:
 src=ROOT/rel;dest=freeze/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dest)
 runtime_data.append(dict(path=rel,sha256=sha(src),frozen_path=str(dest.relative_to(ROOT))))
meta={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'binary':str(a.binary),'binary_sha256':sha(a.binary),
 'compiler_flags':a.compiler_flags,'package_flags':'-package-db dist-newstyle/packagedb/ghc-9.8.4 -package-id Simplicity-0.0.0-inplace-Simplicity-Core -package Simplicity -package jet-discovery',
 'heap_cap_gib':a.heap,'groups':a.group,'source_files':records,'runtime_data':runtime_data,'jobs':[]}
out=data/(a.label+'-full-provenance.json')
out.write_text(json.dumps(meta,indent=2)+'\n')
for group in a.group:
 assert group.replace('-','').isalnum()
 log=data/(a.label+'-'+group+'-verification.txt');cmd=[str(a.binary),group,'+RTS','-N1','-s','-M'+str(a.heap)+'G']
 start=time.monotonic()
 with log.open('w')as f:
  f.write('FROZEN_BINARY_SHA256='+meta['binary_sha256']+'\n');f.flush()
  r=subprocess.run(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
  elapsed=time.monotonic()-start;f.write('\nDIAGNOSTIC_EXIT_STATUS='+str(r.returncode)+'\nDIAGNOSTIC_ELAPSED_SECONDS='+str(elapsed)+'\n')
 row=dict(group=group,actual_exit_status=r.returncode,elapsed_seconds=elapsed,log=str(log.relative_to(ROOT)),log_sha256=sha(log))
 meta['jobs'].append(row);out.write_text(json.dumps(meta,indent=2)+'\n')
 (data/(a.label+'-full-status.json')).write_text(json.dumps(meta['jobs'],indent=2)+'\n')
 print(json.dumps(row),flush=True)
 # Other groups are independent and continue at the same explicit cap. Failed
 # or unfinished groups never inherit a success result from a later group.
meta['ended_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
meta['current_source_changes']=[r['path']for r in records if sha(ROOT/r['path'])!=r['sha256']]
out.write_text(json.dumps(meta,indent=2)+'\n')
