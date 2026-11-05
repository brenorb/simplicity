#!/usr/bin/env python3
"""Run each exact corpus ID in a fresh process, then strictly aggregate.

Build all targets first and freeze the source tree for the entire cohort.
The same frozen executable path/bytes and global source fingerprint are used
for every child and the strict aggregation. --only is development coverage
and never writes the full analysis reports. Existing evidence is preserved.
"""
import argparse
from collections import Counter, deque
from contextlib import ExitStack
import csv
from dataclasses import dataclass
import datetime
import fcntl
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time

ROOT=Path(__file__).resolve().parents[1]
LEGACY_COMMIT='b76b5f16c3194bbffc6f66d6ba496cc5adab268a'
LEGACY_COORDINATOR_SHA256='81efe541a7b87afc8bbfeaab922067fe9a4cf5369e4658ed9f2d4feef8cf2a9a'
ID_PATTERN=r'[A-Za-z0-9][A-Za-z0-9_.-]*'


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


def freeze_executable(original, runner, expected):
    if not runner.exists():
        with tempfile.NamedTemporaryFile(dir=runner.parent,delete=False) as out:
            temporary=Path(out.name)
        try:
            shutil.copy2(original,temporary)
            if sha(temporary)!=expected:
                raise ValueError('original executable changed during freeze')
            try:
                os.link(temporary,runner)
            except FileExistsError:
                pass
        finally:
            temporary.unlink()
    if sha(runner)!=expected:
        raise ValueError('frozen executable hash mismatch')


def count_fresh_passes(log, ident):
    # A source label can contain a literal CR, e.g. the BIP340 CSV comment
    # passed through the Haskell runner. Only LF terminates a process record.
    # Verify a PASS follows the corresponding fresh evaluation record.
    prefix=re.escape(ident.encode())+rb' / '
    evaluate=re.compile(prefix+rb'([^\n]*): evaluating')
    passed=re.compile(prefix+rb'([^\n]*): PASS \([^\n]*\)')
    failed=re.compile(prefix+rb'([^\n]*): FAIL \([^\n]*\)')
    count=0
    pending=None
    for line in log.read_bytes().split(b'\n'):
        start=evaluate.fullmatch(line)
        finish=passed.fullmatch(line)
        if start:
            if pending is not None:
                raise ValueError('evaluation without a preceding vector outcome: '+ident)
            pending=start[1]
        elif finish:
            if pending!=finish[1]:
                raise ValueError('PASS without matching fresh vector evaluation: '+ident)
            count+=1
            pending=None
        elif failed.fullmatch(line):
            raise ValueError('vector failure in purportedly successful log: '+ident)
    if pending is not None:
        raise ValueError('unfinished vector evaluation: '+ident)
    return count


def fresh_passes(log, ident, expected):
    count = count_fresh_passes(log, ident)
    done = (ident+' exact-entry checkpoint verified').encode()
    if count != expected or done not in log.read_bytes().split(b'\n'):
        raise ValueError(f'{ident}: expected {expected} fresh vector passes and the checkpoint marker, found {count} passes')
    return count


def verify_success(item, log, checkpoint, expected):
    ident = item['id']
    if sha(log) != item['log_sha256']:
        raise ValueError('previous successful log changed: '+ident)
    if expected is not None and fresh_passes(log, ident, expected) != item['fresh_vector_passes']:
        raise ValueError('previous fresh vector count changed: '+ident)
    if sha(checkpoint) != item['checkpoint_sha256']:
        raise ValueError('previous successful checkpoint changed: '+ident)


def migrate_legacy(record, raw, expected_sha, directory, checkpoint_dir, counts, coordinator_sha):
    """Admit only the exact signed legacy format after an operator handoff."""
    if hashlib.sha256(raw).hexdigest() != expected_sha:
        raise ValueError('legacy manifest SHA differs from the quiescent handoff')
    if (record['coordinator_sha256'] != LEGACY_COORDINATOR_SHA256
            or record['source_commit_at_start'] != LEGACY_COMMIT
            or not record['complete_registry'] or record['complete']):
        raise ValueError('migration requires the incomplete full cohort from signed b76b5f16')
    blob = subprocess.check_output(
        ['git','show',LEGACY_COMMIT+':jet-discovery/tools/run_isolated.py'], cwd=ROOT)
    signature = subprocess.check_output(
        ['git','show','-s','--format=%G?',LEGACY_COMMIT], cwd=ROOT, text=True).strip()
    if hashlib.sha256(blob).hexdigest() != LEGACY_COORDINATOR_SHA256 or signature != 'G':
        raise ValueError('could not verify the pinned legacy coordinator and its signed commit')

    attempt_numbers = Counter()
    verified = []
    uncredited = []
    for item in record['attempts']:
        ident = item['id']
        if ident not in counts:
            raise ValueError('unexpected legacy ID or aggregation already attempted: '+ident)
        if item['exit_status'] is None:
            raise ValueError('legacy attempt is still open; require recorded child termination: '+ident)
        attempt_numbers[ident] += 1
        log = directory / f'{ident}-attempt{attempt_numbers[ident]}.txt'
        command = item['command']
        if (str(log.relative_to(ROOT)) != item['log'] or log.is_symlink()
                or len(command) != 9
                or command[:6] != [record['runner'],'run-one',ident,'+RTS','-N1','-A16m']
                or not re.fullmatch(r'-M[1-9][0-9]*[MG]',command[6])
                or command[7:] != ['-s','-RTS']):
            raise ValueError('unexpected legacy log or command: '+ident)
        if sha(log) != item['log_sha256']:
            raise ValueError('legacy log bytes changed: '+ident)
        if 'checkpoint_sha256' in item:
            if item['exit_status'] != 0 or ident in verified:
                raise ValueError('inconsistent credited legacy checkpoint: '+ident)
            checkpoint = checkpoint_dir / (ident+'.snapshot')
            verify_success(item, log, checkpoint, counts[ident])
            verified.append(ident)
        else:
            uncredited.append({'id':ident,'log':item['log'],'exit_status':item['exit_status'],
                               'log_sha256_at_handoff':item['log_sha256']})

    archive = directory / ('manifest-before-parallel-'+expected_sha+'.json')
    if archive.exists():
        if archive.read_bytes() != raw:
            raise ValueError('legacy manifest archive changed')
    else:
        with archive.open('xb') as out:
            out.write(raw)
    record['migration'] = {'legacy_commit':LEGACY_COMMIT,
                           'legacy_coordinator_sha256':LEGACY_COORDINATOR_SHA256,
                           'prior_manifest':str(archive.relative_to(ROOT)),
                           'prior_manifest_sha256':expected_sha,
                           'migrated_utc':utc(),
                           'verified_checkpoints':verified,
                           'uncredited_attempts':uncredited}
    record['coordinator_sha256'] = coordinator_sha


@dataclass
class Job:
    process: subprocess.Popen
    item: dict
    log: Path
    started: float


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner',type=Path,required=True)
    parser.add_argument('--label',required=True)
    parser.add_argument('--heap',default='64G')
    parser.add_argument('--jobs',type=int,choices=(1,2),default=1,
                        help='ordinary isolated processes to run concurrently')
    parser.add_argument('--tail-heap',
                        help='per-process cap for sequential --last entries and aggregation; defaults to --heap')
    selection=parser.add_mutually_exclusive_group()
    selection.add_argument('--only',nargs='+',metavar='EXACT_ID')
    selection.add_argument('--last',nargs='+',metavar='EXACT_ID',
                           help='defer selected exact IDs to the end of the full cohort')
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--migrate-b76b5f16',metavar='QUIESCENT_MANIFEST_SHA256',
                        help='explicit --resume handoff from the pinned legacy coordinator after it and its children have exited')
    args=parser.parse_args()
    if not re.fullmatch(ID_PATTERN,args.label):
        parser.error('label must be a simple basename')
    args.tail_heap = args.tail_heap or args.heap
    if any(not re.fullmatch(r'[1-9][0-9]*[MG]',heap) for heap in (args.heap,args.tail_heap)):
        parser.error('heap caps must be RTS sizes such as 64G')
    ordinary_mib = int(args.heap[:-1]) * (1024 if args.heap.endswith('G') else 1)
    if args.jobs == 2 and ordinary_mib > 48*1024:
        parser.error('--jobs 2 requires an ordinary --heap no larger than 48G per child')
    if args.migrate_b76b5f16 and (not args.resume or not args.last
                               or not re.fullmatch(r'[0-9a-f]{64}',args.migrate_b76b5f16)):
        parser.error('--migrate-b76b5f16 requires --resume, the exact --last list, and the old manifest SHA256')
    complete=args.only is None
    source_commit=None
    if complete:
        source_paths=['src','app','vendor-specs','corpus/bips','../Haskell','../C',
                      'jet-discovery.cabal','cabal.project','../Simplicity.cabal']
        tracked=subprocess.run(['git','diff','--quiet','HEAD','--',*source_paths],cwd=ROOT)
        others=subprocess.check_output(['git','ls-files','--others','-z','--',*source_paths],cwd=ROOT).decode().split('\0')
        unmanaged=[name for name in others if name and not
                   (set(Path(name).parts)&{'.git','__pycache__','dist-newstyle'} or
                    name.endswith(('.o','.hi','.dyn_o','.dyn_hi','.DS_Store')))]
        if tracked.returncode or unmanaged:
            raise SystemExit('full cohort requires committed fingerprint inputs; untracked: '+', '.join(unmanaged))
        source_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
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
    freeze_executable(original,runner,binary_hash)
    fingerprint=output(runner,'fingerprint')
    if not re.fullmatch(r'[0-9a-f]{64}',fingerprint):
        raise SystemExit('runner does not provide a valid global fingerprint')
    metadata=subprocess.check_output([str(runner),'metadata'],cwd=ROOT,text=True)
    rows=list(csv.DictReader(io.StringIO(metadata),delimiter='\t'))
    ids=[r['id'] for r in rows]
    if not ids or len(ids)!=len(set(ids)):
        raise SystemExit('empty or duplicate registry IDs')
    if any(not re.fullmatch(ID_PATTERN,i) or i=='strict-aggregation' for i in ids):
        raise SystemExit('registry ID is unsafe or reserved')
    targets=args.only if args.only is not None else ids
    if args.last is not None:
        last=set(args.last)
        if len(last)!=len(args.last) or not last<=set(ids):
            raise SystemExit('every deferred exact ID must occur once in the complete registry')
        targets=[i for i in ids if i not in last]+args.last
    if len(targets)!=len(set(targets)) or not set(targets)<=set(ids):
        raise SystemExit('every selected exact ID must occur once in the complete registry')
    counts={r['id']:int(r['vectors']) for r in rows}
    checkpoint_dir=ROOT/'dist-newstyle/jet-discovery-results'/fingerprint
    # Protect the checkpoint namespace and label even across invocations with
    # different --only lists. Full coordinators also share published reports.
    names=[fingerprint+'.lock','label-'+args.label+'.lock']
    if complete:
        names.append('full-cohort.lock')
    with ExitStack() as locks:
        lock_fds=[]
        for name in names:
            lock=locks.enter_context((binary_dir/name).open('a'))
            try:
                fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
            except BlockingIOError:
                raise SystemExit('another isolated coordinator holds '+name)
            lock_fds.append(lock.fileno())
        try:
            run_cohort(args, runner, original, binary_hash, fingerprint, metadata,
                       targets, counts, source_commit, checkpoint_dir, complete, tuple(lock_fds))
        except (OSError,ValueError,subprocess.CalledProcessError) as error:
            raise SystemExit(str(error))


def run_cohort(args, runner, original, binary_hash, fingerprint, metadata, targets,
               counts, source_commit, checkpoint_dir, complete, lock_fds):
    coordinator_sha = sha(Path(__file__))
    metadata_sha = hashlib.sha256(metadata.encode()).hexdigest()
    deferred = args.last or []
    if complete and not args.resume and any(checkpoint_dir.glob('*.snapshot')):
        raise SystemExit('fresh full cohort requires an empty checkpoint namespace for this fingerprint')
    directory=ROOT/'reports/data'/('isolated-'+args.label)
    directory.mkdir(parents=True,exist_ok=True)
    status=directory/'manifest.json'
    if status.exists():
        if not args.resume:
            raise SystemExit('evidence exists; use a new label or explicit --resume')
        raw = status.read_bytes()
        record=json.loads(raw)
        expected=(fingerprint,str(runner),binary_hash,targets,complete)
        actual=(record['fingerprint'],record['runner'],record['runner_sha256'],record['targets'],record['complete_registry'])
        if (actual!=expected or record['metadata_sha256']!=metadata_sha
                or (directory/'registry.tsv').read_bytes()!=metadata.encode()):
            raise SystemExit('resume requires identical source/binary/path/targets/registry')
        if record.get('fingerprint_breach'):
            raise SystemExit('the previous coordinator observed a fingerprint breach')
        if args.migrate_b76b5f16:
            migrate_legacy(record,raw,args.migrate_b76b5f16,directory,checkpoint_dir,
                           counts,coordinator_sha)
            record['deferred_targets']=deferred
        elif record['coordinator_sha256']!=coordinator_sha or record.get('deferred_targets')!=deferred:
            raise SystemExit('resume requires the same coordinator and deferred IDs, or an explicit supported migration')
    else:
        if args.resume:
            raise SystemExit('no existing cohort to resume')
        record={'started_utc':utc(),'original_runner':str(original),'runner':str(runner),
                'runner_sha256':binary_hash,'fingerprint':fingerprint,
                'coordinator_sha256':coordinator_sha,'build_guard':'runner mtime >= registered sources/settings; not compiler attestation',
                'complete_registry':complete,'source_commit_at_start':source_commit,'registry_rows':len(counts),'targets':targets,
                'deferred_targets':deferred,'metadata_sha256':metadata_sha,
                'attempts':[],'complete':False}
        (directory/'registry.tsv').write_text(metadata)

    def unchanged():
        if not record.get('fingerprint_breach'):
            try:
                if sha(runner)==binary_hash and output(runner,'fingerprint')==fingerprint:
                    return
            except (OSError,subprocess.CalledProcessError):
                pass
            record['fingerprint_breach']=utc()
            atomic(status,record)
        raise ValueError('global source/executable fingerprint could not be verified; cohort stopped')

    def launch(ident,verb,heap):
        attempts=[r for r in record['attempts'] if r['id']==ident]
        log=directory/(ident+f'-attempt{len(attempts)+1}.txt')
        command=[str(runner),verb]+([] if verb=='aggregate' else[ident])+['+RTS','-N1','-A16m','-M'+heap,'-s','-RTS']
        item={'id':ident,'command':command,'started_utc':utc(),'exit_status':None,'log':str(log.relative_to(ROOT))}
        with log.open('xb') as out:
            record['attempts'].append(item)
            atomic(status,record)
            print(f'{ident}: starting isolated process with {heap} heap',flush=True)
            started=time.monotonic()
            try:
                process=subprocess.Popen(command,cwd=ROOT,stdout=out,stderr=subprocess.STDOUT,
                                         start_new_session=True,pass_fds=lock_fds)
            except OSError as error:
                item.update(finished_utc=utc(),log_sha256=sha(log),coordinator_error=str(error))
                atomic(status,record)
                raise
        return Job(process,item,log,started)

    def finish(job, exit_status):
        item,log=job.item,job.log
        ident=item['id']
        item.update(exit_status=exit_status,elapsed_seconds=time.monotonic()-job.started,
                    finished_utc=utc())
        try:
            item['log_sha256']=sha(log)
            unchanged()
            if exit_status:
                raise ValueError(f'exit status {exit_status}')
            if ident!='strict-aggregation':
                if complete:
                    item['fresh_vector_passes']=fresh_passes(log,ident,counts[ident])
                item['checkpoint_sha256']=sha(checkpoint_dir/(ident+'.snapshot'))
        except (OSError,ValueError) as error:
            item['coordinator_error']=str(error)
            print(f'{ident}: failed: {error}; exact log {log}',flush=True)
        else:
            print(ident+': passed, '+str(round(item['elapsed_seconds'],3))+'seconds',flush=True)
        atomic(status,record)
        return 'coordinator_error' not in item

    def preserve_unclaimed(ident):
        checkpoint=checkpoint_dir/(ident+'.snapshot')
        if complete and checkpoint.exists():
            # A crash after child completion but before status publication can
            # leave an unclaimed result. Preserve it, then run that entry anew.
            orphan=checkpoint_dir/('unclaimed-'+args.label)
            orphan.mkdir(exist_ok=True)
            preserved=orphan/(ident+'-'+str(time.time_ns())+'.snapshot')
            checkpoint.rename(preserved)
            print(ident+': preserved unclaimed result; measuring again',flush=True)

    stop_signal=None
    def request_drain(signum, _frame):
        nonlocal stop_signal
        stop_signal=signum

    def batch(ids, slots, heap, verb='run-one'):
        pending=deque(ids)
        running=[]
        failed=False
        def collect():
            nonlocal failed
            for job in list(running):
                code=job.process.poll()
                if code is not None:
                    running.remove(job)
                    if not finish(job,code):
                        failed=True
        try:
            while running or pending:
                collect()
                if failed or stop_signal is not None:
                    if not running:
                        break
                elif pending and len(running)<slots:
                    try:
                        unchanged()
                        # A child may have finished during the fingerprint check.
                        collect()
                        if not failed and stop_signal is None:
                            ident=pending.popleft()
                            if verb=='run-one':
                                preserve_unclaimed(ident)
                            if stop_signal is None:
                                running.append(launch(ident,verb,heap))
                    except (OSError,ValueError) as error:
                        failed=True
                        print(f'coordinator stopped scheduling: {error}',flush=True)
                    continue
                if running:
                    time.sleep(0.25)
        finally:
            # Even unexpected coordinator exceptions leave no child executing
            # after this writer releases the fingerprint lock.
            for job in running:
                job.process.wait()
            collect()
        if stop_signal is not None:
            raise SystemExit(128+stop_signal)
        if failed:
            raise SystemExit('cohort stopped scheduling after failure and drained active jobs')

    signal.signal(signal.SIGINT,request_drain)
    signal.signal(signal.SIGTERM,request_drain)
    unchanged()
    previous={r['id']:r for r in record['attempts']
              if r['exit_status']==0 and 'checkpoint_sha256' in r}
    for ident,item in previous.items():
        verify_success(item,ROOT/item['log'],checkpoint_dir/(ident+'.snapshot'),
                       counts[ident] if complete else None)
        print(ident+': preserved successful checkpoint',flush=True)
    if record['complete']:
        print(record['coverage']+': already completed',flush=True)
        return
    record.setdefault('schedules',[]).append({'started_utc':utc(),'ordinary_jobs':args.jobs,
                                              'ordinary_heap':args.heap,'tail_heap':args.tail_heap})
    atomic(status,record)
    batch((i for i in targets if i not in previous and i not in deferred),args.jobs,args.heap)
    batch((i for i in deferred if i not in previous),1,args.tail_heap)
    if complete:
        # Every exact ID must already have a successful fingerprint-bound
        # checkpoint; aggregate deliberately has no fallback compilation.
        batch(['strict-aggregation'],1,args.tail_heap,'aggregate')
        marker=ROOT/'reports/data/run-fingerprint.txt'
        if not marker.is_file() or marker.read_text().strip()!=fingerprint:
            raise SystemExit('strict aggregation did not publish this cohort fingerprint')
        published=['corpus/README.md','reports/corpus-results.md','reports/whatif.md',
                   'reports/ablations.md','reports/subdags.md','reports/candidate-impact.md','reports/budget-hotspots.md',
                   'reports/data/budget-hotspots.tsv',
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
