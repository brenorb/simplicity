#!/usr/bin/env python3
"""Rank current isolated candidate measurements with explicit scope weights.

Refuses historical/partial results. Invoke with the SAME frozen executable
used by the successful full run; its path participates in the fingerprint.
Writes reproducible intermediate tables, leaving final tier decisions visible
in candidate-ranking-policy.json for review after the full analysis.
"""
import argparse
import collections
import csv
from decimal import Decimal
import hashlib
import io
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'reports/data'


def table(header, rows):
    def cell(x):
        return str(x).replace('|', '\\|').replace('\n', ' ')
    return '\n'.join(['| '+' | '.join(header)+' |',
                      '| '+' | '.join(['---']*len(header))+' |']+
                     ['| '+' | '.join(map(cell, row))+' |' for row in rows])


def read_tsv(path):
    with path.open() as stream:
        return list(csv.DictReader(stream, delimiter='\t'))


def keyed(rows, key):
    result = {r[key]: r for r in rows}
    if len(result) != len(rows):
        raise ValueError('duplicate '+key)
    return result


def context(classification):
    if classification.get('execution_context') == 'client_mode':
        return 'client'
    kind = classification['kind']
    if kind == 'full_spend_condition':
        return 'native_full_spend'
    if kind == 'full_bounded_verifier':
        return 'native_full_verifier'
    if kind == 'protocol_component':
        return 'protocol_component'
    if kind == 'arithmetic_or_hash_kernel':
        return 'kernel'
    raise ValueError('unreviewed classification '+kind)


def wu(value):
    return f'{Decimal(value)/1000:,.3f}'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner', type=Path, required=True,
                        help='same frozen executable path used by the full run')
    args = parser.parse_args()
    runner = args.runner.resolve()
    if not (DATA/'run-fingerprint.txt').is_file():
        raise SystemExit('STALE: no successful complete-run fingerprint exists; run the full corpus before ranking')
    saved = (DATA/'run-fingerprint.txt').read_text().strip()
    current = subprocess.check_output([str(runner), 'fingerprint'],
                                      cwd=ROOT, text=True).strip()
    if not saved or saved != current:
        raise SystemExit('STALE: full-run fingerprint does not match current sources and this executable')
    results = keyed(read_tsv(DATA/'corpus-results.tsv'), 'id')
    metadata = keyed(read_tsv(DATA/'corpus-metadata.tsv'), 'id')
    classes = json.loads((DATA/'corpus-classification.json').read_text())
    policy = json.loads((DATA/'candidate-ranking-policy.json').read_text())
    candidates = policy['candidates']
    emitted = subprocess.check_output([str(runner), 'candidates'], cwd=ROOT, text=True)
    prices = keyed(list(csv.DictReader(io.StringIO(emitted), delimiter='\t')), 'candidate')
    if set(prices) != set(candidates):
        raise ValueError('ranking policy and executable candidate registry differ')
    if set(results) != set(metadata) or not set(results) <= set(classes):
        raise ValueError('incomplete registry, result or classification coverage')
    for ident, row in results.items():
        if row['vectors_ok'] != row['vectors_total'] or row['vectors_total'] != metadata[ident]['vectors']:
            raise ValueError('missing/failed/current vector mismatch: '+ident)
        is_client = context(classes[ident]) == 'client'
        if (row['execution_context'] == 'client-verifier') != is_client:
            raise ValueError('client context disagreement: '+ident)
    impacts = read_tsv(DATA/'candidate-impact.tsv')
    seen = set()
    selected = collections.defaultdict(dict)
    details = collections.defaultdict(list)
    for r in impacts:
        ident, name = r['program'], r['candidate']
        if ident not in results or name not in candidates or (ident, name) in seen:
            raise ValueError('unknown/duplicate isolated-impact row')
        seen.add((ident, name))
        if int(r['current_mwu']) != int(results[ident]['cost_mwu']):
            raise ValueError('impact original bound differs: '+ident)
        saving = int(r['current_mwu'])-int(r['isolated_mwu_estimate'])
        if saving != int(r['saving_mwu']):
            raise ValueError('impact subtraction mismatch')
        kind = context(classes[ident])
        if (r['feasibility_applicable'] == 'false') != (kind == 'client'):
            raise ValueError('client feasibility disagreement: '+ident)
        r = dict(r, scope=kind, count_group=classes[ident]['count_group'])
        details[name].append(r)
        if int(r['occurrences']) <= 0 or saving <= 0:
            continue
        family = candidates[name]['family']
        group = r['count_group']
        old = selected[family].get(group)
        if old is None or saving > int(old['saving_mwu']):
            selected[family][group] = r
    if len(seen) != len(results)*len(candidates):
        raise ValueError('isolated candidate matrix is incomplete')
    ranked = []
    for family in sorted({c['family'] for c in candidates.values()}):
        fronts = [n for n, c in candidates.items() if c['family'] == family]
        rules = [candidates[n] for n in fronts]
        if len({(r['generality'], r['burden'], r['tier']) for r in rules}) != 1:
            raise ValueError('family frontends need consistent ranking policy')
        rule = rules[0]
        rows = list(selected[family].values())
        totals = collections.Counter()
        weighted = Decimal(0)
        for r in rows:
            amount = int(r['saving_mwu'])
            totals[r['scope']] += amount
            weighted += Decimal(amount)*Decimal(str(policy['context_weights'][r['scope']]))
        score = weighted*rule['generality']/rule['burden']/1000
        ranked.append(dict(family=family, frontends=fronts, groups=len(rows),
                           occurrences=sum(int(r['occurrences']) for r in rows),
                           native_mwu=totals['native_full_spend']+totals['native_full_verifier'],
                           client_mwu=totals['client'], component_mwu=totals['protocol_component']+totals['kernel'],
                           weighted_saving_wu=str(weighted/1000), score=str(score),
                           generality=rule['generality'], burden=rule['burden'],
                           tier=rule['tier'], rationale=rule['rationale'], tier_reason=rule['tier_reason']))
    ranked.sort(key=lambda r: Decimal(r['score']), reverse=True)
    (DATA/'candidate-ranking.json').write_text(json.dumps(ranked, indent=2)+'\n')
    with (DATA/'candidate-prices.tsv').open('w', newline='') as out:
        writer = csv.DictWriter(out, ['candidate', 'cost_mwu_estimate', 'method'], delimiter='\t', lineterminator='\n')
        writer.writeheader()
        writer.writerows(prices.values())
    lines = ['# Current candidate ranking evidence', '',
             'All hypothetical prices, overlays, savings and scores are **ESTIMATE**. Original expression bounds are measured. This is a complete isolated-scenario matrix, not a combination of candidate savings.', '',
             policy['score_rule'], '', policy['deduplication'], '',
             'Context weights are explicit judgement: '+json.dumps(policy['context_weights'], sort_keys=True)+'. Static occurrences already affect each measured bound difference; multiplying by occurrences again would double-count that benefit.', '',
             table(['rank', 'family', 'tier', 'deduplicated groups', 'selected occurrences', 'native WU saved ESTIMATE', 'client WU saved ESTIMATE', 'component/kernel WU saved ESTIMATE', 'weighted score', 'generality / burden'],
                   [(i, r['family'], r['tier'], r['groups'], r['occurrences'], wu(r['native_mwu']), wu(r['client_mwu']), wu(r['component_mwu']), f"{Decimal(r['score']):,.3f}", f"{r['generality']} / {r['burden']}") for i, r in enumerate(ranked, 1)]), '',
             '## Every candidate and program', '',
             'The tables retain every program row, including zero matches and negative savings. Feasibility is only the first-vector fixed hypothetical witness budget. Client rows are inapplicable. No candidate has an assigned consensus encoding.', '']
    for name in prices:
        c = candidates[name]
        lines += ['## `'+name+'`', '',
                  '[Specification, C/proof burden and alternatives](../candidates/'+name+'/README.md).', '',
                  'Price: '+wu(prices[name]['cost_mwu_estimate'])+'WU **ESTIMATE**. '+prices[name]['method'], '',
                  c['rationale']+' Tier: '+c['tier']+'. '+c['tier_reason'], '',
                  table(['program / count group', 'scope', 'occurrences', 'current WU', 'isolated WU ESTIMATE', 'WU saved ESTIMATE', 'fixed hypothetical fit before / after'],
                        [(r['program']+' / '+r['count_group'], r['scope'], r['occurrences'], wu(r['current_mwu']), wu(r['isolated_mwu_estimate']), wu(r['saving_mwu']),
                          'n/a (client)' if r['scope']=='client' else ('yes' if int(r['current_mwu'])<=1000*int(r['assumed_budget_wu']) else 'no')+' / '+('yes' if int(r['isolated_mwu_estimate'])<=1000*int(r['assumed_budget_wu']) else 'no'))
                         for r in details[name]]), '']
    (ROOT/'reports/candidate-ranking.md').write_text('\n'.join(lines)+'\n')
    inputs = ['run-fingerprint.txt', 'corpus-results.tsv', 'corpus-metadata.tsv',
              'corpus-classification.json', 'candidate-impact.tsv', 'candidate-ranking-policy.json']
    manifest = {'run_fingerprint': saved, 'runner': str(runner),
                'runner_sha256': hashlib.sha256(runner.read_bytes()).hexdigest(),
                'inputs': {p: hashlib.sha256((DATA/p).read_bytes()).hexdigest() for p in inputs},
                'tool_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'programs': len(results), 'candidate_frontends': len(prices),
                'families': len(ranked), 'isolated_rows': len(impacts)}
    (DATA/'candidate-ranking-provenance.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps({k: manifest[k] for k in ['programs', 'candidate_frontends', 'families', 'isolated_rows']}))


if __name__ == '__main__':
    main()
