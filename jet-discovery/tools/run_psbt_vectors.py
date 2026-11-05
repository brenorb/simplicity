#!/usr/bin/env python3
"""Record exact local sources, inputs and one bounded actual PSBT vector run."""
from pathlib import Path
import argparse,datetime,hashlib,json,shutil,subprocess,time
parser=argparse.ArgumentParser()
parser.add_argument('--heap-gib',type=int,default=3)
args=parser.parse_args()
if not 1<=args.heap_gib<=64:parser.error('heap bound outside 1..64 GiB')
root=Path(__file__).resolve().parents[1];data=root/'reports/data';name=f'psbt-full23-{args.heap_gib}g'
frozen=data/(name+'-freeze');build=Path('/private/tmp/psbt-reference-build');binary=Path('/private/tmp/psbt-smoke')
if frozen.exists():raise SystemExit('refusing to overwrite existing run snapshot')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=[root/'src'/p.relative_to(build).with_suffix('.hs')for p in build.rglob('*.hi')if p.name!='Main.hi']
sources += [root/'tools'/n for n in ['PsbtSmoke.hs','PsbtReference.hs','extract_psbt_vectors.py','run_psbt_vectors.py']]
inputs=[p for p in (root/'vendor-specs/bitcoin-growth9').iterdir()if p.is_file()]
inputs += [root/f'vendor-specs/bitcoin-growth{n}/bip-{b}.mediawiki'for n,b in [(3,'0174'),(3,'0370'),(2,'0143')]]
records=[]
for source in sorted(set(sources+inputs)):
 path=source.relative_to(root);dest=frozen/path;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
 records.append({'path':str(path),'sha256':sha(source),'snapshot':str(dest.relative_to(root))})
executable=Path('/private/tmp')/(name+'-frozen')/'psbt-smoke';executable.parent.mkdir(exist_ok=True);shutil.copy2(binary,executable)
command=[str(executable),'+RTS','-N1','-A16m',f'-M{args.heap_gib}G','-s','-RTS']
manifest=data/(name+'-provenance.json');log=data/(name+'-rts.txt')
record=dict(scope='23 exact native PSBT per-session finalizer/extractor vectors; no cost/registry credit before pass',compiler='GHC9.8.4 -O1 -w -threaded -rtsopts -isrc with local dist-newstyle/packagedb/ghc-9.8.4',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),command=command,binary_sha256=sha(executable),inputs=records)
manifest.write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic()
with log.open('wb')as stream:result=subprocess.run(command,cwd=root,stdout=stream,stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode,elapsed_seconds=time.monotonic()-start,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),log_sha256=sha(log),source_unchanged_at_end=all(sha(root/r['path'])==r['sha256']for r in records))
manifest.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({k:v for k,v in record.items()if k!='inputs'},indent=2))
raise SystemExit(result.returncode)
