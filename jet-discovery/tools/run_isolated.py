#!/usr/bin/env python3
"""Run each exact corpus ID in a fresh process, then strictly aggregate.

Build all targets first and freeze the source tree for the entire cohort.
The same frozen executable path/bytes and global source fingerprint are used
for every child and the strict aggregation. --only is development coverage
and never writes the full analysis reports. Existing evidence is preserved.
"""
import argparse
import csv
import datetime
import hashlib
import io
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT=Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def output(runner,*args):
    return subprocess.check_output([str(runner),*args],cwd=ROOT,text=True).strip()


def atomic(path,value):
    temporary=path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value,indent=2)+'\n')
    temporary.replace(path)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner',type=Path,required=True)
    parser.add_argument('--label',required=True)
    parser.add_argument('--heap',default='64G')
    selection=parser.add_mutually_exclusive_group()
    selection.add_argument('--only',nargs='+',metavar='EXACT_ID')
    selection.add_argument('--last',nargs='+',metavar='EXACT_ID',
                           help='defer selected exact IDs to the end of the full cohort')
    parser.add_argument('--resume',action='store_true')
    args=parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*',args.label):
        parser.error('label must be a simple basename')
    if not re.fullmatch(r'[1-9][0-9]*[MG]',args.heap):
        parser.error('heap must be an RTS size such as64G')
    original=args.runner.resolve()
    if not original.is_file():
        parser.error('runner executable is missing')
    # A cheap additional stale-build guard, not compiler attestation. Cabal
    # must still build the current library/executable before starting.
    cabal=ROOT/'jet-discovery.cabal'
    section=cabal.read_text().split('exposed-modules:',1)[1].split('executable jet-discovery',1)[0]
    modules=re.findall(r'JetDiscovery(?:\.[A-Za-z0-9]+)+',section)
    sources=[ROOT/'src'/Path(m.replace('.','/')).with_suffix('.hs') for m in modules]
    sources += [ROOT/'app/Main.hs',cabal,ROOT/'cabal.project']
    newer=[str(p.relative_to(ROOT)) for p in sources if p.stat().st_mtime_ns>original.stat().st_mtime_ns]
    if newer:
        raise SystemExit('build runner after registered sources/settings: '+', '.join(newer))
    binary_hash=sha(original)
    binary_dir=ROOT/'dist-newstyle/isolated-runners'
    binary_dir.mkdir(parents=True,exist_ok=True)
    runner=binary_dir/(binary_hash+'-jet-discovery')
    if runner.exists():
        if sha(runner)!=binary_hash:
            raise SystemExit('frozen executable hash mismatch')
    else:
        shutil.copy2(original,runner)
    fingerprint=output(runner,'fingerprint')
    if not re.fullmatch(r'[0-9a-f]{64}',fingerprint):
        raise SystemExit('runner does not provide a valid global fingerprint')
    metadata=output(runner,'metadata')+'\n'
    rows=list(csv.DictReader(io.StringIO(metadata),delimiter='\t'))
    ids=[r['id'] for r in rows]
    if not ids or len(ids)!=len(set(ids)):
        raise SystemExit('empty or duplicate registry IDs')
    targets=args.only if args.only is not None else ids
    if args.last is not None:
        last=set(args.last)
        if len(last)!=len(args.last) or not last<=set(ids):
            raise SystemExit('every deferred exact ID must occur once in the complete registry')
        targets=[i for i in ids if i not in last]+args.last
    if len(targets)!=len(set(targets)) or not set(targets)<=set(ids):
        raise SystemExit('every selected exact ID must occur once in the complete registry')
    complete=args.only is None
    directory=ROOT/'reports/data'/('isolated-'+args.label)
    directory.mkdir(parents=True,exist_ok=True)
    status=directory/'manifest.json'
    if status.exists():
        if not args.resume:
            raise SystemExit('evidence exists; use a new label or explicit --resume')
        record=json.loads(status.read_text())
        expected=(fingerprint,str(runner),binary_hash,targets,complete)
        actual=(record['fingerprint'],record['runner'],record['runner_sha256'],record['targets'],record['complete_registry'])
        if actual!=expected or record['coordinator_sha256']!=sha(Path(__file__)) or record['metadata_sha256']!=hashlib.sha256(metadata.encode()).hexdigest():
            raise SystemExit('resume requires identical source/binary/path/targets/coordinator')
    else:
        if args.resume:
            raise SystemExit('no existing cohort to resume')
        record={'started_utc':utc(),'original_runner':str(original),'runner':str(runner),
                'runner_sha256':binary_hash,'fingerprint':fingerprint,
                'coordinator_sha256':sha(Path(__file__)),'build_guard':'runner mtime >= registered sources/settings; not compiler attestation',
                'complete_registry':complete,'registry_rows':len(ids),'targets':targets,
                'metadata_sha256':hashlib.sha256(metadata.encode()).hexdigest(),
                'attempts':[],'complete':False}
        (directory/'registry.tsv').write_text(metadata)
        atomic(status,record)

    def unchanged():
        if sha(runner)!=binary_hash or output(runner,'fingerprint')!=fingerprint:
            raise SystemExit('global source/executable fingerprint changed; cohort stopped')

    def launch(ident,verb):
        unchanged()
        attempts=[r for r in record['attempts'] if r['id']==ident]
        log=directory/(ident+f'-attempt{len(attempts)+1}.txt')
        command=[str(runner),verb]+([] if verb=='aggregate' else[ident])+['+RTS','-N1','-A16m','-M'+args.heap,'-s','-RTS']
        item={'id':ident,'command':command,'started_utc':utc(),'exit_status':None,'log':str(log.relative_to(ROOT))}
        record['attempts'].append(item);atomic(status,record)
        print(ident+': starting isolated process',flush=True)
        started=time.monotonic()
        with log.open('wb')as out:
            result=subprocess.run(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT)
        item.update(exit_status=result.returncode,elapsed_seconds=time.monotonic()-started,
                    finished_utc=utc(),log_sha256=sha(log))
        atomic(status,record)
        unchanged()
        if result.returncode:
            raise SystemExit(ident+': failed; exact log '+str(log))
        if verb=='run-one':
            checkpoint=ROOT/'dist-newstyle/jet-discovery-results'/fingerprint/(ident+'.snapshot')
            item['checkpoint_sha256']=sha(checkpoint)
        atomic(status,record)
        print(ident+': passed, '+str(round(item['elapsed_seconds'],3))+'seconds',flush=True)

    unchanged()
    for ident in targets:
        previous=[r for r in record['attempts'] if r['id']==ident and r['exit_status']==0 and 'checkpoint_sha256'in r]
        checkpoint=ROOT/'dist-newstyle/jet-discovery-results'/fingerprint/(ident+'.snapshot')
        if previous:
            if not checkpoint.is_file() or sha(checkpoint)!=previous[-1]['checkpoint_sha256']:
                raise SystemExit('previous successful checkpoint changed/missing: '+ident)
            print(ident+': preserved successful checkpoint',flush=True)
            continue
        launch(ident,'run-one')
    if complete:
        # Every exact ID must already have a successful fingerprint-bound
        # checkpoint; aggregate deliberately has no fallback compilation.
        launch('strict-aggregation','aggregate')
        marker=ROOT/'reports/data/run-fingerprint.txt'
        if not marker.is_file() or marker.read_text().strip()!=fingerprint:
            raise SystemExit('strict aggregation did not publish this cohort fingerprint')
        published=['corpus/README.md','reports/corpus-results.md','reports/whatif.md',
                   'reports/ablations.md','reports/subdags.md','reports/candidate-impact.md',
                   'reports/data/corpus-results.tsv','reports/data/candidate-impact.tsv',
                   'reports/data/subdags-exact.tsv','reports/data/subdags-shape.tsv',
                   'reports/data/run-fingerprint.txt']
        record['published_sha256']={name:sha(ROOT/name) for name in published}
    unchanged()
    record.update(complete=True,finished_utc=utc(),coverage='complete registry' if complete else'development subset; full reports not generated')
    atomic(status,record)
    print(record['coverage']+': completed',flush=True)


if __name__=='__main__':
    main()
