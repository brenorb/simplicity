#!/usr/bin/env python3
"""Freeze the local dependency closure, then run one BIP47 client at16GiB."""
from pathlib import Path
import datetime,hashlib,json,shutil,subprocess,time
root=Path(__file__).resolve().parents[1]
out=root/'reports/data';frozen=out/'payment-code-full16g-freeze'
binary=Path('/private/tmp/payment-code-smoke')
build=Path('/private/tmp/payment-code-smoke-build')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if frozen.exists():raise SystemExit('refusing to overwrite an existing diagnostic snapshot')
sources=[root/'src'/p.relative_to(build).with_suffix('.hs')for p in build.rglob('*.hi')if p.name!='Main.hi']
sources += [root/p for p in ['tools/PaymentCodeSmoke.hs','tools/PaymentCodeReference.hs','tools/HmacByteReference.hs','tools/extract_bip47_vectors.py','tools/run_payment_code_vectors.py']]
inputs=list((root/'vendor-specs/bitcoin-growth8').glob('*'))
inputs += [root/'vendor-specs/bitcoin-growth7'/n for n in ['manifest.json','bip47-vectors-gist.md','bip47-hmac-order-comparison.json']]
inputs += [root/'vendor-specs/bitcoin-growth3/bip-0047.mediawiki']
records=[]
for source in sorted(set(sources+inputs)):
 if not source.is_file():raise SystemExit('missing diagnostic dependency '+str(source))
 name=source.relative_to(root);dest=frozen/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,dest)
 records.append({'path':str(name),'sha256':sha(source),'snapshot':str(dest.relative_to(root))})
frozen_binary=frozen/'payment-code-smoke';shutil.copyfile(binary,frozen_binary);frozen_binary.chmod(0o755)
command=[str(frozen_binary),'+RTS','-N1','-M16G','-s','-RTS']
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'actual BIP47 private-client19 full vectors, canonical CMR and prepared kernel per-vector checks; no full-corpus or measured WU claim','command':command,'binary_sha256':sha(frozen_binary),'inputs':records}
manifest=out/'payment-code-full16g-provenance.json';manifest.write_text(json.dumps(record,indent=2)+'\n')
start=time.monotonic()
with(out/'payment-code-full16g-rts.txt').open('wb')as log:
 result=subprocess.run(command,cwd=root,stdout=log,stderr=subprocess.STDOUT)
record.update(exit_code=result.returncode,elapsed_seconds=time.monotonic()-start,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),log_sha256=sha(out/'payment-code-full16g-rts.txt'),source_unchanged_at_end=all(sha(root/r['path'])==r['sha256']for r in records))
manifest.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k!='inputs'},indent=2))
raise SystemExit(result.returncode)
