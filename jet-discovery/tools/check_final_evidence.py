#!/usr/bin/env python3
"""Check the complete local run or its independently signed publication."""
import argparse
import collections
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tempfile

from coverage_report import INPUTS as COVERAGE_INPUTS
from publish_recommendations import STARK_FIELDS, STARK_ID, STARK_ROOTS, STARK_SNAPSHOT, STARK_STAGES, publication_paths
from run_isolated import count_fresh_passes
from stark_stage_profile import summarize as stark_stages

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'reports/data'
BASELINE='3f0bb69c4547bcf3483ca5ccbd06699464166650'
SIGNER_KEY='ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIPmM1X+xTTu6UoYpRM5zVPs5Puz/Pp3zAocHb30jSaEI'
SIGNER_FINGERPRINT='SHA256:vWChnu0aP/mLy250+2dB3DTtfl1AMBYuTvw4xvVTG+c'
RANKING_INPUTS={'run-fingerprint.txt','corpus-results.tsv','corpus-metadata.tsv',
                'corpus-classification.json','candidate-impact.tsv','candidate-ranking-policy.json'}
HANDOFFS={
    'migration':('parallel','b76b5f16c3194bbffc6f66d6ba496cc5adab268a',
                 '81efe541a7b87afc8bbfeaab922067fe9a4cf5369e4658ed9f2d4feef8cf2a9a'),
    'overlap_migration':('overlap','3838c177ba31a59bd471eed7352df7538fc809c8',
                         '1b9fced8b94984a4332b85a0ed79ac67ae14b05688ec6471676b2577c80f803c'),
}


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_tsv(path, read=Path.read_bytes):
    return list(csv.DictReader(io.StringIO(read(path).decode(),newline=None),delimiter='\t'))


class SignedPublication:
    """Verify working copies against the regular-file blobs in the signed tip."""

    def __init__(self, git):
        self.git=git
        self.commit=git('rev-parse','HEAD')
        self.root=Path(git('rev-parse','--show-toplevel')).resolve()
        self.object_format=git('rev-parse','--show-object-format')
        self.require_signed(self.commit)
        self.require_ancestor(BASELINE)
        changes=git('diff','--no-renames','--name-only',BASELINE,self.commit).splitlines()
        require(changes and all(name.startswith('jet-discovery/') for name in changes),
                'Signed commit changes files outside jet-discovery')
        self.blobs={}
        tree=subprocess.check_output(['git','ls-tree','-r','-z','--full-tree',self.commit],cwd=ROOT)
        for record in tree.decode().split('\0'):
            if record:
                info,name=record.split('\t',1)
                mode,kind,oid=info.split()
                if kind=='blob' and mode in {'100644','100755'}:
                    self.blobs[name]=oid

    def require_signed(self, commit):
        require(re.fullmatch(r'[0-9a-f]{40}',commit),'Expected an exact signed commit ID')
        # The public key and fingerprint come from the pinned signed run
        # source. A fresh checkout needs no personal allowed-signers file.
        with tempfile.NamedTemporaryFile(mode='w') as allowed:
            allowed.write('jet-discovery '+SIGNER_KEY+'\n')
            allowed.flush()
            signature=self.git('-c','gpg.format=ssh','-c','gpg.ssh.allowedSignersFile='+allowed.name,
                               'show','-s','--format=%G? %GF',commit)
        require(signature=='G '+SIGNER_FINGERPRINT,'Invalid publication or frozen-source signature: '+commit)

    def require_ancestor(self, commit):
        require(subprocess.run(['git','merge-base','--is-ancestor',commit,self.commit],
                               cwd=ROOT).returncode==0,'Commit is outside the publication history: '+commit)

    def read(self, path):
        resolved=path.resolve()
        require(resolved.is_relative_to(self.root) and not path.is_symlink(),
                'Published evidence path is outside the signed tree: '+str(path))
        name=resolved.relative_to(self.root).as_posix()
        require(name in self.blobs,'Evidence file is absent from the signed tree: '+name)
        data=path.read_bytes()
        blob=hashlib.new(self.object_format)
        blob.update(f'blob {len(data)}\0'.encode())
        blob.update(data)
        require(blob.hexdigest()==self.blobs[name],'Evidence bytes differ from the signed tree: '+name)
        return data


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cohort',required=True,type=Path,help='terminal isolated full run manifest')
    parser.add_argument('--harness',required=True,type=Path,help='terminal unfiltered local Tasty run record')
    parser.add_argument('--published-only',action='store_true',
                        help='verify signed HEAD, archived logs and reports without local binaries or checkpoints')
    args=parser.parse_args()
    git=lambda *args: subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
    publication=SignedPublication(git) if args.published_only else None
    read=publication.read if publication else Path.read_bytes
    evidence_sha=lambda path: hashlib.sha256(read(path)).hexdigest()
    load_json=lambda path: json.loads(read(path))
    if publication:
        read(Path(__file__))
    cohort=load_json(args.cohort)
    require(cohort['complete_registry'] and cohort['complete'],'The isolated run is incomplete')
    require(cohort['coordinator_sha256']==evidence_sha(ROOT/'tools/run_isolated.py'),'Coordinator differs from the completed run')
    runner=Path(cohort['runner'])
    fp=cohort['fingerprint']
    require(re.fullmatch(r'[0-9a-f]{64}',fp) and
            fp==read(DATA/'run-fingerprint.txt').decode().strip(),'Final fingerprint mismatch')
    if not publication:
        require(sha(runner)==cohort['runner_sha256'],'The frozen executable changed')
        current=subprocess.check_output([str(runner),'fingerprint'],cwd=ROOT,text=True).strip()
        require(current==fp,'Final fingerprint mismatch')
    manifest_files={'corpus/README.md','reports/corpus-results.md','reports/whatif.md','reports/ablations.md',
                    'reports/subdags.md','reports/candidate-impact.md','reports/budget-hotspots.md',
                    'reports/data/budget-hotspots.tsv','reports/data/corpus-results.tsv',
                    'reports/data/candidate-impact.tsv','reports/data/subdags-exact.tsv',
                    'reports/data/subdags-shape.tsv','reports/data/run-fingerprint.txt'}
    require(set(cohort['published_sha256'])==manifest_files,'Core published table inventory is incomplete')
    for name,digest in cohort['published_sha256'].items():
        require(evidence_sha(ROOT/name)==digest,'A core published table changed: '+name)
    rows=read_tsv(DATA/'corpus-results.tsv',read)
    ids={r['id'] for r in rows}
    require(len(rows)==len(ids)==cohort['registry_rows']==len(cohort['targets']) and ids==set(cohort['targets']),
            'Registry, isolated target and result IDs differ')
    metadata=read_tsv(DATA/'corpus-metadata.tsv',read)
    require(evidence_sha(DATA/'corpus-metadata.tsv')==cohort['metadata_sha256']==
            evidence_sha(args.cohort.parent/'registry.tsv'),'Registry metadata changed after run')
    counts={r['id']:int(r['vectors']) for r in metadata}
    require(len(metadata)==len(counts)==len(ids) and ids==set(counts) and
            all(int(r['vectors_ok'])==int(r['vectors_total'])==counts[r['id']]>0 for r in rows),
            'Missing or failed vector evidence')
    unrecorded_logs=0
    for item in cohort['attempts']:
        log=ROOT/item['log']
        require('checkpoint_sha256' not in item or item['exit_status']==0,
                'Failed attempt claims a checkpoint: '+item['id'])
        if 'log_sha256' in item:
            require(evidence_sha(log)==item['log_sha256'],'Execution log changed: '+item['id'])
        else:
            require(item['exit_status'] is None and 'checkpoint_sha256' not in item,
                    'Terminal or credited attempt lacks a log hash: '+item['id'])
            if log.exists():
                read(log)
            unrecorded_logs+=1
    successes={r['id']:r for r in cohort['attempts'] if r['exit_status']==0}
    require(set(successes)==ids|{'strict-aggregation'},'Missing successful exact-entry execution')
    aggregate_log=read(ROOT/successes['strict-aggregation']['log']).split(b'\n')
    require(f'all {len(ids)} corpus programs pass their vectors; complete analysis published'.encode() in aggregate_log,
            'Strict aggregation did not record complete publication')
    for ident,item in successes.items():
        if ident in ids:
            require(item['fresh_vector_passes']==counts[ident]==count_fresh_passes(ROOT/item['log'],ident),
                    'Missing fresh per-vector execution: '+ident)
            require(re.fullmatch(r'[0-9a-f]{64}',item['checkpoint_sha256']),'Missing checkpoint hash: '+ident)
            if not publication:
                checkpoint=ROOT/'dist-newstyle/jet-discovery-results'/fp/(ident+'.snapshot')
                require(sha(checkpoint)==item['checkpoint_sha256'],'Checkpoint changed: '+ident)
    classes=load_json(DATA/'corpus-classification.json')
    groups={classes[i]['count_group'] for i in ids}
    full={classes[i]['count_group'] for i in ids if classes[i]['kind'].startswith('full_')}
    require(len(groups)>=150 and len(full)*2>len(groups),'Insufficient distinct or full groups')
    cmr_groups=collections.defaultdict(set)
    for r in rows:
        cmr_groups[r['cmr']].add(classes[r['id']]['count_group'])
    conflicts={cmr:sorted(gs) for cmr,gs in cmr_groups.items() if len(gs)>1}
    if conflicts:
        # The default and APO entries use the same outer checkSigVerify' leaf
        # but different disconnected modes. The standalone proof hashes each
        # witness-free mode and tests actual response to an outpoint mutation.
        modes=load_json(DATA/'disconnected-sighash-identities.json')
        log=ROOT/modes['log']
        require(modes['exit_status']==0 and evidence_sha(log)==modes['log_sha256'],'Disconnected-mode probe is missing')
        for name in ['src/JetDiscovery/Corpus/Baseline.hs','src/JetDiscovery/Corpus/CovenantMisc.hs',
                     'tools/DisconnectedSighashProbe.hs']:
            require(evidence_sha(ROOT/name)==modes['source_sha256'][name],'Disconnected-mode source changed: '+name)
        fields=dict(line.split('=',1) for line in read(log).decode().splitlines()[:4])
        require(fields['actual_outpoint_mutation_distinguishes_modes']=='True' and
                fields['sig_all_mode_identity']!=fields['apo_mode_identity'],
                'Disconnected-mode proof does not establish distinct behavior')
        allowed={fields['outer_CMR'].removeprefix('0x'):['baseline-p2pk-sigall','bip118-apo']}
        require(conflicts==allowed,'Unreviewed exact CMR reused across groups: '+json.dumps(conflicts))

    harness=load_json(args.harness)
    harness_log=ROOT/harness['log']
    require(harness['exit_status']==0 and evidence_sha(harness_log)==harness['log_sha256'],'Local harness failed or changed')
    require(not any(s=='-p' or s.startswith('--pattern') for s in harness['command']),'Local harness was filtered')
    if not publication:
        require(sha(ROOT/harness['frozen_executable'])==harness['executable_sha256'],'Local test executable changed')
    tasty=re.search(r'^All (\d+) tests passed',read(harness_log).decode(),re.M)
    require(tasty and int(tasty.group(1))>=45,'Complete current Tasty suite is missing')
    harness_sources={str(path.relative_to(ROOT)) for folder in ('src','app','test')
                     for path in (ROOT/folder).rglob('*.hs')}|{'cabal.project','jet-discovery.cabal'}
    source_scope=lambda name: name.startswith(('app/','src/','test/')) or name in {'cabal.project','jet-discovery.cabal'}
    require({name for name in harness['source_sha256'] if source_scope(name)}==harness_sources,
            'Local harness source inventory differs')
    vendor_inputs={str(path.relative_to(ROOT)) for path in (ROOT/'vendor-specs').rglob('*') if path.is_file()}
    require(set(harness['input_sha256'])==vendor_inputs,'Local harness vendor inventory differs')
    for name,digest in harness['source_sha256'].items():
        if source_scope(name):
            require(evidence_sha(ROOT/name)==digest,'Current harness source differs: '+name)
    for name,digest in harness['input_sha256'].items():
        require(evidence_sha(ROOT/name)==digest,'Current harness input differs: '+name)

    upstream=load_json(DATA/'upstream-validation-status.json')
    for key,(kind,legacy,script_sha) in HANDOFFS.items():
        migration=cohort.get(key)
        if migration is None:
            continue
        prior=ROOT/migration['prior_manifest']
        digest=migration['prior_manifest_sha256']
        require(prior.resolve()==args.cohort.resolve().parent/('manifest-before-'+kind+'-'+digest+'.json')
                and not prior.is_symlink() and evidence_sha(prior)==digest,
                'Archived '+kind+' coordinator manifest differs')
        old=load_json(prior)
        require(old['complete_registry'] and not old['complete'] and
                all(item['exit_status'] is not None for item in old['attempts']),
                'Handoff did not preserve a quiescent partial cohort: '+kind)
        immutable=('fingerprint','runner','runner_sha256','source_commit_at_start','metadata_sha256','registry_rows','targets')
        require(all(old[k]==cohort[k] for k in immutable) and
                old['attempts']==cohort['attempts'][:len(old['attempts'])],
                'Handoff changed original run identity or attempts: '+kind)
        require(migration['legacy_commit']==legacy,'Unexpected legacy coordinator commit: '+kind)
        if publication:
            publication.require_signed(legacy)
            publication.require_ancestor(legacy)
        else:
            require(git('show','-s','--format=%G?',legacy)=='G','Invalid legacy coordinator signature: '+kind)
        if key=='migration':
            require(legacy==old['source_commit_at_start'],'Serial coordinator differs from the frozen source commit')
        else:
            require(old.get('migration')==cohort.get('migration') and
                    old['schedules']==cohort['schedules'][:len(old['schedules'])],
                    'Overlap handoff changed the earlier handoff or schedules')
        blob=subprocess.check_output(['git','show',legacy+':jet-discovery/tools/run_isolated.py'],cwd=ROOT)
        require(hashlib.sha256(blob).hexdigest()==script_sha==old['coordinator_sha256']==migration['legacy_coordinator_sha256'],
                'Signed coordinator source differs: '+kind)
        credited=[item['id'] for item in old['attempts'] if 'checkpoint_sha256' in item]
        uncredited=[{'id':item['id'],'log':item['log'],'exit_status':item['exit_status'],
                     'log_sha256_at_handoff':item['log_sha256']}
                    for item in old['attempts'] if 'checkpoint_sha256' not in item]
        require(credited==migration['verified_checkpoints'] and
                uncredited==migration['uncredited_attempts'] and
                all(evidence_sha(ROOT/item['log'])==item['log_sha256'] for item in old['attempts']),
                'Archived checkpoint or log evidence differs: '+kind)
    if not publication:
        require(git('branch','--show-current')=='feat/bitcoin-jet-discovery','Unexpected branch')
        require(git('remote','get-url','fork')=='https://github.com/brenorb/simplicity.git','Unexpected fork remote')
        changed=git('diff','master','--name-only').splitlines()
        require(changed and all(name.startswith('jet-discovery/') for name in changed),'Diff extends beyond jet-discovery')
    freeze=cohort['source_commit_at_start']
    if publication:
        publication.require_signed(freeze)
        publication.require_ancestor(freeze)
    tip=[publication.commit] if publication else []
    require(not git('diff',freeze,*tip,'--name-only','--','src','app','vendor-specs','corpus/bips',
                    'cabal.project','jet-discovery.cabal','../C','../Haskell','../Simplicity.cabal'),
            'Tracked fingerprint inputs differ from the start commit')
    require(git('rev-parse','HEAD:C')==upstream['c_tree'] and git('rev-parse','HEAD:Haskell')==upstream['haskell_tree'],
            'Upstream suite source trees changed')
    require(upstream['test_filter']=='none' and 'default' in upstream['quickcheck_cases'],'Upstream filters changed')
    upstream_runs={r['name']:r for r in upstream['runs']}
    for name,expect in [('upstream-c-default-check',r'^Successes: 98\nFailures: 0$'),
                        ('upstream-haskell-default-tests',r'^All 3252 tests passed')]:
        run=upstream_runs[name]; log=ROOT/run['log']
        require(run['exit_status']==0 and evidence_sha(log)==run['sha256'] and re.search(expect,read(log).decode(),re.M),
                'Unchanged upstream suite evidence failed: '+name)

    prices=read_tsv(DATA/'candidate-prices.tsv',read)
    impacts=read_tsv(DATA/'candidate-impact.tsv',read)
    names={r['candidate'] for r in prices}
    require(len(prices)==len(names) and len(impacts)==len(ids)*len(names) and
            {(r['program'],r['candidate']) for r in impacts}=={(ident,name) for ident in ids for name in names},
            'Incomplete candidate matrix')
    budgets={r['program']:int(r['assumed_budget_wu']) for r in impacts}
    cap_text=read(ROOT.parent/'C/limitations.h').decode()
    cap=int(re.search(r'^#define BUDGET_MAX (\d+)U$',cap_text,re.M).group(1))
    require(all(int(r['maximum_budget_wu'])==cap and
                int(r['effective_budget_wu'])==min(cap,budgets[r['program']]) and
                int(r['assumed_budget_wu'])==budgets[r['program']] for r in impacts),
            'Candidate budget evidence disagrees with the actual C cap')
    over={r['id']:int(r['cost_mwu']) for r in rows if r['execution_context']!='client-verifier'
          and int(r['cost_mwu'])>1000*min(cap,budgets[r['id']])}
    by_program=collections.Counter()
    for r in read_tsv(DATA/'budget-hotspots.tsv',read):
        ident=r['program']
        require(ident in over and int(r['native_mwu'])==over[ident] and
                int(r['assumed_budget_wu'])==budgets[ident] and int(r['maximum_budget_wu'])==cap,
                'Incorrect over-budget cost-driver row: '+ident)
        by_program[ident]+=int(r['exclusive_mwu'])
    require(dict(by_program)==over,'Exclusive cost drivers do not partition every over-budget bound')
    ranked=load_json(DATA/'candidate-ranking.json')
    require({n for r in ranked for n in r['frontends']}==names and
            all(r['tier'] in ('strong','maybe','rejected') and r['tier_reason'] for r in ranked),'Pending recommendation tier')
    for name in names:
        readme=ROOT/'candidates'/name/'README.md'
        require(fp in read(readme).decode(),'No fresh README evidence for '+name)
    derived=load_json(DATA/'recommendations-publication.json')
    cohort_path=args.cohort.resolve()
    require(cohort_path.is_relative_to(ROOT) and
            derived.get('cohort_path')==cohort_path.relative_to(ROOT).as_posix() and
            derived.get('cohort_sha256')==evidence_sha(cohort_path),
            'Derived publication identifies a different terminal cohort')
    require(derived['fingerprint']==fp and derived['runner']==str(runner) and
            derived['runner_sha256']==cohort['runner_sha256'] and
            derived['publisher_sha256']==evidence_sha(ROOT/'tools/publish_recommendations.py'),
            'Derived publication has a different fingerprint, runner or publisher')
    require(set(derived['files'])==set(publication_paths(names)),'Derived publication inventory incomplete')
    for name,digest in derived['files'].items():
        require(evidence_sha(ROOT/name)==digest,'A derived published report changed: '+name)
    if STARK_ID in ids:
        row=next(r for r in rows if r['id']==STARK_ID)
        stage_profile=stark_stages(STARK_ROOTS,STARK_FIELDS,STARK_SNAPSHOT)
        require(stage_profile==load_json(STARK_STAGES) and stage_profile['fingerprint']==fp and
                stage_profile['cmr']==row['cmr'] and stage_profile['full_native_mwu']==int(row['cost_mwu']) and
                stage_profile['snapshot_sha256']==successes[STARK_ID]['checkpoint_sha256'],
                'Published STARK stage breakdown or checkpoint differs from the measured cohort')
    ranking_record=load_json(DATA/'candidate-ranking-provenance.json')
    require(ranking_record['run_fingerprint']==fp and ranking_record['runner']==str(runner) and
            ranking_record['runner_sha256']==cohort['runner_sha256'] and
            ranking_record['tool_sha256']==evidence_sha(ROOT/'tools/rank_candidates.py'),
            'Ranking provenance differs from the published run')
    require(set(ranking_record['inputs'])==RANKING_INPUTS,'Ranking provenance input inventory differs')
    for name,digest in ranking_record['inputs'].items():
        require(evidence_sha(DATA/name)==digest,'Ranking input changed: '+name)
    recommendations=ROOT/'reports/RECOMMENDATIONS.md'
    require(fp in read(recommendations).decode(),'Missing final recommendations')
    sources=collections.Counter(r['source_set'] for r in read_tsv(DATA/'source-cost-coverage.tsv',read))
    expected={'open-bip':24,'unnumbered-proposal':10,'protocol-tvl':40,'protocol-tvl-non-cex':40,
              'ethereum-gas':117,'ethereum-24h-aws':20,'solana-compute':64,'solana-24h-soltop':20}
    require(sources==expected,'Incomplete named per-source evidence')
    coverage_record=load_json(DATA/'coverage-input-hashes.json')
    require(set(coverage_record)==set(COVERAGE_INPUTS)|{'reports/data/run-fingerprint.txt','reports/data/candidate-impact.tsv'},
            'Per-source table input inventory differs')
    for name,digest in coverage_record.items():
        require(evidence_sha(ROOT/name)==digest,'Per-source table input changed: '+name)
    status=('signed published evidence verified' if publication else
            'complete local evidence verified; signed fork push checked separately')
    print(json.dumps(dict(status=status,audit_mode='published-only' if publication else 'local',
                          signed_publication_commit=publication.commit if publication else None,
                          publication_signer_fingerprint=SIGNER_FINGERPRINT if publication else None,
                          comparison_baseline=BASELINE if publication else git('rev-parse','master'),
                          run_fingerprint_recomputed=not publication,
                          frozen_runner_bytes_checked=not publication,checkpoint_bytes_checked=not publication,
                          harness_executable_bytes_checked=not publication,
                          published_stark_checkpoint_and_stage_costs_checked=STARK_ID in ids,
                          attempts_without_runtime_log_digest=unrecorded_logs,
                          fingerprint=fp,registered=len(ids),groups=len(groups),full_groups=len(full),
                          vectors=sum(counts.values()),candidate_frontends=len(names),candidate_families=len(ranked),
                          isolated_scenarios=len(impacts),source_rows=dict(sources),harness_tests=int(tasty.group(1)),
                          upstream_c=98,upstream_haskell=3252,cohort_sha256=evidence_sha(args.cohort),
                          coordinator_handoff_sha256=cohort.get('migration',{}).get('prior_manifest_sha256'),
                          overlap_handoff_sha256=cohort.get('overlap_migration',{}).get('prior_manifest_sha256'),
                          harness_provenance_sha256=evidence_sha(args.harness),recommendations_sha256=evidence_sha(recommendations),
                          scope='all tracked differences from master under jet-discovery/'),indent=2))


if __name__=='__main__':
    main()
