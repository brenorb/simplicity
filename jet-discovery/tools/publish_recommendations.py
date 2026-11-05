#!/usr/bin/env python3
"""Render verified final recommendations and exact per-candidate README evidence."""
import argparse
import collections
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from rank_candidates import ROOT, DATA, context, keyed, read_tsv, table, wu

START = '<!-- final-corpus-evidence:start -->'
END = '<!-- final-corpus-evidence:end -->'
TIERS = ('strong', 'maybe', 'rejected')


def publication_paths(names):
    core = ['reports/RECOMMENDATIONS.md','reports/bip-verdicts.md','reports/candidate-ranking.md',
            'reports/coverage-and-costs.md','reports/data/candidate-ranking.json',
            'reports/data/candidate-prices.tsv','reports/data/candidate-ranking-provenance.json',
            'reports/data/coverage-input-hashes.json','reports/data/corpus-coverage.tsv',
            'reports/data/source-cost-coverage.tsv','reports/data/bn254-groth16-estimate.json']
    return sorted(core+['candidates/'+name+'/README.md' for name in names])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()



def fits(row):
    if row['feasibility_applicable'] == 'false':
        return 'n/a (client)'
    budget = int(row['effective_budget_wu'])
    before = int(row['current_mwu']) <= budget*1000
    after = int(row['isolated_mwu_estimate']) <= budget*1000
    return f"{'yes' if before else 'no'} / {'yes' if after else 'no'} at {budget} WU"


def candidate_readme(path, name, rule, price, rows, fp):
    matches = [r for r in rows if int(r['matched_dag_nodes']) > 0 or int(r['saving_mwu']) != 0]
    lines = [START, '', '## Final corpus evidence', '', f'Full-run fingerprint: `{fp}`.', '',
             f"**{rule['tier'].capitalize()}**: {rule['tier_reason']}", '',
             f"Price: **{wu(price['cost_mwu_estimate'])} WU (ESTIMATE)**. {price['method']}", '',
             f"Matches in {len(matches)} of {len(rows)} registered rows: "
             f"{sum(int(r['matched_dag_nodes']) for r in matches):,} matched DAG nodes across all branches, "
             f"{sum(int(r['occurrences']) for r in matches):,} selected-path occurrences before family deduplication.", '']
    if matches:
        lines += [table(['program','scope','selected occurrences','matched DAG nodes','native WU','isolated WU ESTIMATE','saved WU ESTIMATE','fixed hypothetical fit before / after'],
                       [(r['program'],r['scope'],r['occurrences'],r['matched_dag_nodes'],wu(r['current_mwu']),wu(r['isolated_mwu_estimate']),wu(r['saving_mwu']),fits(r))
                        for r in matches]), '']
    else:
        lines += ['No exact DAG matches in the verified corpus.', '']
    lines += [f'See the [complete matrix](../../reports/candidate-ranking.md#{name}) for zero-match rows and competing scenarios. '
              'The budget scenario holds the original first-vector stack fixed and caps it at the in-tree maximum. There is no candidate encoding, '
              'measured C price, or consensus feasibility claim.', '', END]
    block = '\n'.join(lines)
    original = path.read_text()
    if START in original or END in original:
        if original.count(START) != 1 or original.count(END) != 1 or original.index(START)>original.index(END):
            raise SystemExit('Invalid generated block markers in '+str(path))
        before, rest = original.split(START,1)
        _, after = rest.split(END,1)
        return before+block+after
    title, _, body = original.partition('\n')
    if not title.startswith('# '):
        raise SystemExit('Missing candidate title in '+str(path))
    prose = body.lstrip('\n').splitlines()
    if prose and prose[0].startswith('**Corpus evidence withdrawn pending the fresh complete run.**'):
        prose[0] = 'The specification and earlier examples below predate the complete run. Use the verified matrix above for current corpus claims.'
    return title+'\n\n'+block+'\n\n'+'\n'.join(prose)+'\n'


def final_report(fp, policy, ranked, results, groups, full):
    vectors = sum(int(r['vectors_ok']) for r in results.values())
    lines = ['# Recommendations: missing Bitcoin Simplicity jets', '',
             f'The verified corpus contains **{len(results)} programs in {len(groups)} distinct groups**, including '
             f'**{len(full)} full bounded applications or verifiers**. All **{vectors:,} vectors** passed. '
             'This report recommends what to prototype and benchmark; it changes no consensus jet.', '',
             f'Run fingerprint: `{fp}`. Reproduce with [METHOD.md](METHOD.md). See [all program results](corpus-results.md), '
             '[sub-DAG mining](subdags.md), [over-budget cost drivers](budget-hotspots.md), [combined overlays](whatif.md), [ablations](ablations.md), '
             '[all source comparisons](coverage-and-costs.md) and [the complete candidate matrix](candidate-ranking.md).', '',
             '## Ranked candidate families', '',
             'Native static bounds are measured. All hypothetical prices, savings and scores are **ESTIMATE**. '
             'Occurrences refer to the worst path after repricing. Matched groups also include off-path nodes. A positive saving can remain when the new worst path has zero occurrences.', '',
             policy['score_rule'], '', policy['deduplication'], '']
    for tier in TIERS:
        rows = [(i,r) for i,r in enumerate(ranked,1) if r['tier']==tier]
        lines += ['### '+tier.capitalize(), '']
        if not rows:
            lines += ['No candidates assigned to this tier.', '']
            continue
        lines += [table(['overall rank','reference prototypes','matched groups','saving groups','saving groups with zero selected occurrences','selected occurrences in scored rows','native WU saved ESTIMATE',
                         'client WU saved ESTIMATE','component/kernel WU saved ESTIMATE','score','generality / burden','reason'],
                        [(i,', '.join(f'[{n}](../candidates/{n}/README.md)' for n in r['frontends']),r['matched_groups'],r['groups'],r['zero_selected_saving_groups'],r['occurrences'],
                          wu(r['native_mwu']),wu(r['client_mwu']),wu(r['component_mwu']),f"{Decimal(r['score']):,.3f}",
                          f"{r['generality']} / {r['burden']}",r['tier_reason']) for i,r in rows]), '']
    lines += ['## Cost-only and unprototyped concepts', '',
              '[BIP341 hash access](../candidates/bip341_hashes/README.md) has a separately priced cost-only stand-in in '
              '[whatif.md](whatif.md), outside the executable exact-expression overlays. '
              '[Whole P-256 verify](../candidates/p256_ecdsa_verify/README.md) and '
              '[monolithic SHRINCS](../candidates/shrincs_verify/README.md) remain concepts. These three concepts receive '
              'no measured matches or ranking score.', '',
              (ROOT/'reports/bip-verdicts.md').read_text().split('\n',1)[1].strip(), '',
              '## Limits that affect these recommendations', '',
              '- Bitcoin execution receives its budget from the caller. Witness stack bytes + 50 is a stated scenario. '
              'Fit applies the in-tree cap. Client verifiers have no onchain fit result. The first-vector stack and native program encoding are held '
              'fixed because a hypothetical jet has no assigned encoding.',
              '- Static bounds are not latency. Selected-path counts are not network call frequencies. The corpus '
              'and context weights affect the order; C benchmarks and proofs could change the tier decisions.',
              '- The [full STARK](FIBONACCI-STARK.md) measures one custom M31 AIR/DEEP/FRI profile and has no '
              'verified security level or Stone, Circle or Stwo wire compatibility. The [BN254 result](bn254-groth16.md) '
              'measures field arithmetic and estimates one dense pairing arithmetic component.',
              '- The [period inventories](PERIOD-RANKINGS.md) have distinct datasets, windows and attribution rules. '
              'Their source associations do not establish foreign deployment or implementation equivalence.',
              '- The [eprint scan](eprint-scan.md) distinguishes keyword metadata triage, individually reviewed text '
              'and primary-source gaps. Complete published inventories can include vectors outside the native bounds.', '']
    return '\n'.join(lines)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner',required=True,type=Path,
                        help='same frozen executable used to complete the isolated run')
    runner=parser.parse_args().runner.resolve()
    if not runner.is_file():
        raise SystemExit('Missing frozen corpus executable')
    fp=subprocess.check_output([str(runner),'fingerprint'],cwd=ROOT,text=True).strip()
    saved=DATA/'run-fingerprint.txt'
    if not saved.is_file() or not fp or saved.read_text().strip()!=fp:
        raise SystemExit('STALE: final recommendations require the successful full-run fingerprint')
    policy=json.loads((DATA/'candidate-ranking-policy.json').read_text())
    for name,rule in policy['candidates'].items():
        if rule['tier'] not in TIERS or not rule['tier_reason'].strip() or rule['tier_reason'].startswith('Assign after'):
            raise SystemExit('Review and assign a final tier and reason for '+name)
    for script in ('rank_candidates.py','coverage_report.py'):
        subprocess.run([sys.executable,str(ROOT/'tools'/script),'--runner',str(runner)],cwd=ROOT,check=True)
    ranked=json.loads((DATA/'candidate-ranking.json').read_text())
    prices=keyed(read_tsv(DATA/'candidate-prices.tsv'),'candidate')
    results=keyed(read_tsv(DATA/'corpus-results.tsv'),'id')
    classes=json.loads((DATA/'corpus-classification.json').read_text())
    if not set(results)<=set(classes):
        raise SystemExit('Every actual result must have an explicit classification')
    # The retired FRI fragment remains classified for historical tables only.
    classes={ident:classes[ident] for ident in results}
    groups={c['count_group'] for c in classes.values()}
    full={c['count_group'] for c in classes.values() if c['kind'].startswith('full_')}
    if len(groups)<150 or 2*len(full)<=len(groups):
        raise SystemExit('Final recommendations require 150 groups and a majority of full applications/verifiers')
    impacts=collections.defaultdict(list)
    for r in read_tsv(DATA/'candidate-impact.tsv'):
        impacts[r['candidate']].append(dict(r,scope=context(classes[r['program']])))
    changes={}
    for name,price in prices.items():
        path=ROOT/'candidates'/name/'README.md'
        changes[path]=candidate_readme(path,name,policy['candidates'][name],price,impacts[name],fp)
    changes[ROOT/'reports/RECOMMENDATIONS.md']=final_report(fp,policy,ranked,results,groups,full)
    bn_estimate=subprocess.check_output([sys.executable,str(ROOT/'tools/bn254_extrapolate.py'),
                                         '--runner',str(runner)],cwd=ROOT,text=True)
    changes[DATA/'bn254-groth16-estimate.json']=bn_estimate
    publication=DATA/'recommendations-publication.json'
    if publication.exists():
        publication.unlink()
    for path,contents in changes.items():
        tmp=path.with_name(path.name+'.new')
        tmp.write_text(contents)
        tmp.replace(path)
    current=subprocess.check_output([str(runner),'fingerprint'],cwd=ROOT,text=True).strip()
    if current!=fp:
        raise SystemExit('Source fingerprint changed during derived publication')
    record=dict(fingerprint=fp,runner=str(runner),runner_sha256=sha(runner),
                publisher_sha256=sha(Path(__file__)),
                files={name:sha(ROOT/name) for name in publication_paths(prices)})
    pending=publication.with_suffix('.json.new')
    pending.write_text(json.dumps(record,indent=2)+'\n')
    pending.replace(publication)
    print(f'Published {len(prices)} candidate evidence blocks and recommendations for {len(groups)} groups')


if __name__=='__main__':
    main()
