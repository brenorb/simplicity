#!/usr/bin/env python3
"""Check the complete same-source corpus, ranking, and unchanged upstream tests."""
import argparse
import collections
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess

from publish_recommendations import publication_paths

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'reports/data'


def require(ok, message):
    if not ok:
        raise SystemExit(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_tsv(path):
    with path.open() as src:
        return list(csv.DictReader(src,delimiter='\t'))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cohort',required=True,type=Path,help='terminal isolated full run manifest')
    parser.add_argument('--harness',required=True,type=Path,help='terminal unfiltered local Tasty run record')
    args=parser.parse_args()
    cohort=json.loads(args.cohort.read_text())
    require(cohort['complete_registry'] and cohort['complete'],'The isolated run is incomplete')
    require(cohort['coordinator_sha256']==sha(ROOT/'tools/run_isolated.py'),'Coordinator differs from the completed run')
    runner=Path(cohort['runner'])
    require(sha(runner)==cohort['runner_sha256'],'The frozen executable changed')
    fp=subprocess.check_output([str(runner),'fingerprint'],cwd=ROOT,text=True).strip()
    require(fp==cohort['fingerprint']==(DATA/'run-fingerprint.txt').read_text().strip(),'Final fingerprint mismatch')
    manifest_files={'corpus/README.md','reports/corpus-results.md','reports/whatif.md','reports/ablations.md',
                    'reports/subdags.md','reports/candidate-impact.md','reports/budget-hotspots.md',
                    'reports/data/budget-hotspots.tsv','reports/data/corpus-results.tsv',
                    'reports/data/candidate-impact.tsv','reports/data/subdags-exact.tsv',
                    'reports/data/subdags-shape.tsv','reports/data/run-fingerprint.txt'}
    require(set(cohort['published_sha256'])==manifest_files,'Core published table inventory is incomplete')
    for name,digest in cohort['published_sha256'].items():
        require(sha(ROOT/name)==digest,'A core published table changed: '+name)
    rows=read_tsv(DATA/'corpus-results.tsv')
    ids={r['id'] for r in rows}
    require(len(rows)==len(ids)==cohort['registry_rows']==len(cohort['targets']) and ids==set(cohort['targets']),
            'Registry, isolated target and result IDs differ')
    metadata=read_tsv(DATA/'corpus-metadata.tsv')
    require(sha(DATA/'corpus-metadata.tsv')==cohort['metadata_sha256'],'Registry metadata changed after run')
    counts={r['id']:int(r['vectors']) for r in metadata}
    require(ids==set(counts) and all(int(r['vectors_ok'])==int(r['vectors_total'])==counts[r['id']]>0 for r in rows),
            'Missing or failed vector evidence')
    successes={r['id']:r for r in cohort['attempts'] if r['exit_status']==0}
    require(set(successes)==ids|{'strict-aggregation'},'Missing successful exact-entry execution')
    for ident,item in successes.items():
        require(sha(ROOT/item['log'])==item['log_sha256'],'Execution log changed: '+ident)
        if ident in ids:
            require(item['fresh_vector_passes']==counts[ident],'Missing fresh per-vector execution: '+ident)
            checkpoint=ROOT/'dist-newstyle/jet-discovery-results'/fp/(ident+'.snapshot')
            require(sha(checkpoint)==item['checkpoint_sha256'],'Checkpoint changed: '+ident)
    classes=json.loads((DATA/'corpus-classification.json').read_text())
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
        modes=json.loads((DATA/'disconnected-sighash-identities.json').read_text())
        log=ROOT/modes['log']
        require(modes['exit_status']==0 and sha(log)==modes['log_sha256'],'Disconnected-mode probe is missing')
        for name in ['src/JetDiscovery/Corpus/Baseline.hs','src/JetDiscovery/Corpus/CovenantMisc.hs',
                     'tools/DisconnectedSighashProbe.hs']:
            require(sha(ROOT/name)==modes['source_sha256'][name],'Disconnected-mode source changed: '+name)
        fields=dict(line.split('=',1) for line in log.read_text().splitlines()[:4])
        require(fields['actual_outpoint_mutation_distinguishes_modes']=='True' and
                fields['sig_all_mode_identity']!=fields['apo_mode_identity'],
                'Disconnected-mode proof does not establish distinct behavior')
        allowed={fields['outer_CMR'].removeprefix('0x'):['baseline-p2pk-sigall','bip118-apo']}
        require(conflicts==allowed,'Unreviewed exact CMR reused across groups: '+json.dumps(conflicts))

    harness=json.loads(args.harness.read_text())
    harness_log=ROOT/harness['log']
    require(harness['exit_status']==0 and sha(harness_log)==harness['log_sha256'],'Local harness failed or changed')
    require(not any(s=='-p' or s.startswith('--pattern') for s in harness['command']),'Local harness was filtered')
    require(sha(ROOT/harness['frozen_executable'])==harness['executable_sha256'],'Local test executable changed')
    tasty=re.search(r'^All (\d+) tests passed',harness_log.read_text(),re.M)
    require(tasty and int(tasty.group(1))>=43,'Complete current Tasty suite is missing')
    for name,digest in harness['source_sha256'].items():
        if name.startswith(('app/','src/','test/')) or name in {'cabal.project','jet-discovery.cabal'}:
            require(sha(ROOT/name)==digest,'Current harness source differs: '+name)
    for name,digest in harness['input_sha256'].items():
        require(sha(ROOT/name)==digest,'Current harness input differs: '+name)

    upstream=json.loads((DATA/'upstream-validation-status.json').read_text())
    git=lambda *args: subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
    require(git('branch','--show-current')=='feat/bitcoin-jet-discovery','Unexpected branch')
    require(git('remote','get-url','fork')=='https://github.com/brenorb/simplicity.git','Unexpected fork remote')
    changed=git('diff','master','--name-only').splitlines()
    require(changed and all(name.startswith('jet-discovery/') for name in changed),'Diff extends beyond jet-discovery')
    freeze=cohort['source_commit_at_start']
    require(not git('diff',freeze,'--name-only','--','src','app','vendor-specs','corpus/bips',
                    'cabal.project','jet-discovery.cabal','../C','../Haskell','../Simplicity.cabal'),
            'Tracked fingerprint inputs differ from the start commit')
    require(git('rev-parse','HEAD:C')==upstream['c_tree'] and git('rev-parse','HEAD:Haskell')==upstream['haskell_tree'],
            'Upstream suite source trees changed')
    require(upstream['test_filter']=='none' and 'default' in upstream['quickcheck_cases'],'Upstream filters changed')
    upstream_runs={r['name']:r for r in upstream['runs']}
    for name,expect in [('upstream-c-default-check',r'^Successes: 98\nFailures: 0$'),
                        ('upstream-haskell-default-tests',r'^All 3252 tests passed')]:
        run=upstream_runs[name]; log=ROOT/run['log']
        require(run['exit_status']==0 and sha(log)==run['sha256'] and re.search(expect,log.read_text(),re.M),
                'Unchanged upstream suite evidence failed: '+name)

    prices=read_tsv(DATA/'candidate-prices.tsv')
    impacts=read_tsv(DATA/'candidate-impact.tsv')
    names={r['candidate'] for r in prices}
    require(len(impacts)==len(ids)*len(names) and len({(r['program'],r['candidate']) for r in impacts})==len(impacts),
            'Incomplete candidate matrix')
    budgets={r['program']:int(r['assumed_budget_wu']) for r in impacts}
    cap_text=(ROOT.parent/'C/limitations.h').read_text()
    cap=int(re.search(r'^#define BUDGET_MAX (\d+)U$',cap_text,re.M).group(1))
    over={r['id']:int(r['cost_mwu']) for r in rows if r['execution_context']!='client-verifier'
          and int(r['cost_mwu'])>1000*min(cap,budgets[r['id']])}
    by_program=collections.Counter()
    for r in read_tsv(DATA/'budget-hotspots.tsv'):
        ident=r['program']
        require(ident in over and int(r['native_mwu'])==over[ident] and
                int(r['assumed_budget_wu'])==budgets[ident] and int(r['maximum_budget_wu'])==cap,
                'Incorrect over-budget cost-driver row: '+ident)
        by_program[ident]+=int(r['exclusive_mwu'])
    require(dict(by_program)==over,'Exclusive cost drivers do not partition every over-budget bound')
    ranked=json.loads((DATA/'candidate-ranking.json').read_text())
    require({n for r in ranked for n in r['frontends']}==names and
            all(r['tier'] in ('strong','maybe','rejected') and r['tier_reason'] for r in ranked),'Pending recommendation tier')
    for name in names:
        readme=ROOT/'candidates'/name/'README.md'
        require(fp in readme.read_text(),'No fresh README evidence for '+name)
    derived=json.loads((DATA/'recommendations-publication.json').read_text())
    require(derived['fingerprint']==fp and derived['runner']==str(runner) and
            derived['runner_sha256']==cohort['runner_sha256'] and
            derived['publisher_sha256']==sha(ROOT/'tools/publish_recommendations.py'),
            'Derived publication has a different fingerprint, runner or publisher')
    require(set(derived['files'])==set(publication_paths(names)),'Derived publication inventory incomplete')
    for name,digest in derived['files'].items():
        require(sha(ROOT/name)==digest,'A derived published report changed: '+name)
    ranking_record=json.loads((DATA/'candidate-ranking-provenance.json').read_text())
    require(ranking_record['run_fingerprint']==fp and ranking_record['runner']==str(runner) and
            ranking_record['runner_sha256']==cohort['runner_sha256'] and
            ranking_record['tool_sha256']==sha(ROOT/'tools/rank_candidates.py'),
            'Ranking provenance differs from the published run')
    for name,digest in ranking_record['inputs'].items():
        require(sha(DATA/name)==digest,'Ranking input changed: '+name)
    recommendations=ROOT/'reports/RECOMMENDATIONS.md'
    require(fp in recommendations.read_text(),'Missing final recommendations')
    sources=collections.Counter(r['source_set'] for r in read_tsv(DATA/'source-cost-coverage.tsv'))
    expected={'open-bip':24,'unnumbered-proposal':10,'protocol-tvl':40,'protocol-tvl-non-cex':40,
              'ethereum-gas':117,'ethereum-24h-aws':20,'solana-compute':64,'solana-24h-soltop':20}
    require(sources==expected,'Incomplete named per-source evidence')
    for name,digest in json.loads((DATA/'coverage-input-hashes.json').read_text()).items():
        require(sha(ROOT/name)==digest,'Per-source table input changed: '+name)
    print(json.dumps(dict(status='complete local evidence verified; signed fork push checked separately',
                          fingerprint=fp,registered=len(ids),groups=len(groups),full_groups=len(full),
                          vectors=sum(counts.values()),candidate_frontends=len(names),candidate_families=len(ranked),
                          isolated_scenarios=len(impacts),source_rows=dict(sources),harness_tests=int(tasty.group(1)),
                          upstream_c=98,upstream_haskell=3252,cohort_sha256=sha(args.cohort),
                          harness_provenance_sha256=sha(args.harness),recommendations_sha256=sha(recommendations),
                          scope='all tracked differences from master under jet-discovery/'),indent=2))


if __name__=='__main__':
    main()
