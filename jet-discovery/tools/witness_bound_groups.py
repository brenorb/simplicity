#!/usr/bin/env python3
"""Sequential capped vector diagnostics; record actual executable exit status."""
import json,subprocess,sys,time
from pathlib import Path
root=Path(__file__).resolve().parents[1]
if len(sys.argv)<2:
 raise SystemExit('usage: witness_bound_groups.py /absolute/compiled-diagnostic [group ...]')
binary=sys.argv[1]
groups=sys.argv[2:] or ['lms-kat','lms','xmss','shrincs-stateful','shrincs-stateless']
results=[]
for group in groups:
 target=root/'reports/data'/f'{group}-witness-bound.txt'
 begin=time.monotonic()
 with target.open('w') as log:
  proc=subprocess.run([binary,group,'+RTS','-s','-M8G'],cwd=root,stdout=log,stderr=subprocess.STDOUT)
  elapsed=time.monotonic()-begin
  log.write(f'\nDIAGNOSTIC_EXIT_STATUS={proc.returncode}\nDIAGNOSTIC_ELAPSED_SECONDS={elapsed:.3f}\n')
 results.append(dict(group=group,exit_status=proc.returncode,elapsed_seconds=elapsed,log=str(target.relative_to(root))))
 (root/'reports/data/witness-bound-status.json').write_text(json.dumps(results,indent=2)+'\n')
 print(group,proc.returncode,f'{elapsed:.2f}s',flush=True)
if any(r['exit_status'] for r in results):
 raise SystemExit(1)
