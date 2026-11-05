#!/usr/bin/env python3
"""Join every inventoried source row to actual runner costs without guessing.

Export metadata with the built runner first. Without --runner, the source
inventory is generated with costs pending. Verified costs require the same
frozen executable as the successful full run. This script never executes a
Simplicity expression or substitutes a related protocol for the named source.
Mappings labelled PROXY are explicitly architectural associations, not ports.
"""
import argparse,csv,collections,hashlib,io,json,subprocess
from decimal import Decimal
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'reports/data'
INPUTS=['reports/data/corpus-metadata.tsv','reports/data/corpus-results.tsv',
        'reports/data/corpus-classification.json','reports/data/bip-program-map.json',
        'reports/data/unnumbered-proposal-map.json','vendor-specs/bip-inventory/proposals/sources.json',
        'vendor-specs/bip-inventory/softfork-triage.tsv',
        'reports/data/protocol-ranking.tsv','reports/data/protocol-ranking-non-cex.tsv','reports/data/ethereum-gas-ranking.tsv',
        'reports/data/solana-compute-ranking.tsv','reports/data/growth-backlog.tsv',
        'tools/coverage_report.py']
PERIOD_DIR='vendor-specs/rankings/soltop-2026-11-05'
INPUTS += [PERIOD_DIR+'/top20.tsv',PERIOD_DIR+'/utxo-triage.tsv',PERIOD_DIR+'/manifest.json','reports/PERIOD-RANKINGS.md']


def read_tsv(path):
    return list(csv.DictReader((ROOT/path).open(),delimiter='\t',lineterminator='\n'))


def cell(s):
    return str(s).replace('|','\\|').replace('\n',' ').replace('\r',' ')


def table(head,rows):
    return '\n'.join(['| '+' | '.join(head)+' |','| '+' | '.join(['---']*len(head))+' |']+
                     ['| '+' | '.join(cell(x) for x in row)+' |' for row in rows])


def wu(mwu):
    return f'{Decimal(mwu)/1000:,.3f}'


def classify_contract(dataset,r):
    """Every rule preserves named source identity and carries its exact gap."""
    if dataset in ['protocol-tvl','protocol-tvl-non-cex']:
        cat=r['category']
        if cat=='CEX':
            return [],'NOT_A_CONTRACT','Custodial holdings are not an enforceable contract port; reserve/liability attestations require a separately specified statement.'
        if cat in ['Lending','CDP']:
            return ['ethsol-lending-liquidation','app-median-oracle-settlement'],'PROXY_NATIVE_COLLATERAL','Bounded BTC liquidation/oracle settlement patterns only; named protocol debt accrual, assets, collateral configuration and full state machine are not implemented.'
        if cat in ['Liquid Staking','Staking Pool','Restaking']:
            return ['app-babylon-unbonding','app-babylon-slashing'],'PROXY_CUSTODY','Bitcoin authorization/unbond/slash pattern only; foreign validator selection, rewards and consensus/slash evidence are not verified.'
        if cat in ['Bridge','Canonical Bridge']:
            return ['xchain-secp256k1-ecdsa','xchain-keccak-merkle-membership'],'PROXY_COMPONENTS','Generic signature/Merkle components only; protocol-specific message format, finality, replay protection and bridge payout covenant are not implemented.'
        if cat=='Dexs':
            return ['xchain-uniswap-v2-amount-out','xchain-fullmath-muldiv'],'PROXY_AMM_ARITHMETIC','Constant-product/full-width arithmetic demand only; named pool formula, fee schedule, token ledger and complete swap covenant are not ported.'
        if cat=='Derivatives':
            return ['app-perpetual-funding-settlement'],'PROXY_FUNDING','Native collateral funding settlement only; named exchange positions, prices, liquidation, insurance and order matching are not implemented.'
        if cat in ['Basis Trading','RWA']:
            return ['app-reserve-preserving-spend','app-median-oracle-settlement'],'PROXY_ATTESTED_CUSTODY','Only custody/attested-price patterns measured; issuer redemption, external reserves, hedge positions and solvency remain external.'
        return [],'UNMAPPED','Source category does not identify a complete enforceable Bitcoin predicate; protocol source review and explicit state/asset model required.'
    if dataset=='ethereum-gas' and r.get('has_execution_code')=='False':
        return [],'NO_RETRIEVED_EXECUTION_CODE','No bytecode at the sampled block. Do not infer a contract port or an EOA solely from empty bytecode; native/precompile behavior needs separate identification.'
    label=r['label']
    if label.startswith('Unclassified'):
        return [],'UNCLASSIFIED',r.get('utxo_verdict_reason','Unclassified implementation; no mapping inferred from address/selector or compute total.')
    if dataset=='ethereum-gas':
        if label in ['USDT','USDC']:
            return [],'UNIMPLEMENTED_TOKEN_TRANSITION','Transfer/approval storage and issuer controls are not ported. The ERC2612 entry must not be presented as an implementation of these observed transfer calls.'
        if label in ['Uniswap Universal Router','Uniswap v3 SwapRouter','Uniswap SwapRouter02']:
            return ['xchain-uniswap-v3-tick-math','xchain-fullmath-muldiv'],'RELATED_EXACT_LIBRARY_KERNELS','Exact Uniswap arithmetic kernels measured; observed routing commands, pool execution and complete UTXO asset transitions are not implemented or attributed from the receipt.'
        if label=='ERC4337 EntryPoint v0.7':
            return ['ethsol-safe-allowance'],'PROXY_AUTHORIZATION_POLICY','A bounded Bitcoin allowance wallet is a policy comparison; EntryPoint nonce/storage, validation callbacks, paymaster and gas accounting are unimplemented.'
        if label=='Multicall3':
            return [],'ROUTING_NOT_A_NEW_PRIMITIVE','Call/read batching is not itself a new cryptographic verifier. Inner calls need trace-based identification; top-level receipts do not establish them.'
    if dataset in ['solana-compute','solana-24h-soltop']:
        if label in ['PumpSwap AMM','Meteora DAMM v2']:
            return ['xchain-uniswap-v2-amount-out','xchain-fullmath-muldiv'],'PROXY_AMM_ARITHMETIC','AMM arithmetic proxy only; source-specific reserves, fees, invariant and asset/output transition are not ported.'
        if label=='Pump.fun':
            return [],'UNIMPLEMENTED_BONDING_CURVE','Bonding-curve transition and explicit asset conservation model not implemented; no Uniswap proxy is silently substituted.'
        if label=='SPL Associated Token Account':
            return [],'NOT_DIRECTLY_APPLICABLE','Solana-specific account-address derivation; Bitcoin output ownership is different. No full port is claimed.'
        if label=='SPL Token-2022':
            return [],'UNIMPLEMENTED_TOKEN_TRANSITION','Transfer authorization can map to outputs, but source extensions, mint/supply and exact asset semantics are not implemented.'
        if label=='Pump fee program':
            return ['app-royalty-payment-splitter'],'PROXY_FEE_ALLOCATION','Fixed native payment splitter is only an allocation comparison; actual Pump fee rates, tiers and instruction state are not implemented.'
        if label in ['Orca Whirlpool','Raydium CLMM']:
            return ['xchain-uniswap-v3-tick-math'],'PROXY_TICK_ARITHMETIC','Exact Uniswap Q96 kernel; source-specific Q64 rounding/fee/position semantics and complete pool covenant remain missing.'
        if label=='Jupiter v6 aggregator':
            return [],'UNIMPLEMENTED_ROUTE','No chosen route/pool state is established from provider CU; general cross-program routing and mutable pool accounts are not a complete Bitcoin covenant.'
        if label=='Meteora DLMM':
            return [],'UNIMPLEMENTED_BIN_TRANSITION','Bin-based prices/liquidity/fees and serialized asset/reserve state are not implemented; Uniswap TickMath is not silently substituted.'
    return [],'UNMAPPED','Label lacks an explicit reviewed corpus mapping; preserve source row and review its implementation before drawing a conclusion.'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runner',type=Path,help='same frozen executable as the successful full corpus run')
    args=parser.parse_args()
    metadata=read_tsv('reports/data/corpus-metadata.tsv')
    if not metadata:
        raise SystemExit('Empty corpus metadata: export it from the built runner first')
    meta={r['id']:r for r in metadata}
    if len(meta)!=len(metadata):
        raise SystemExit('Duplicate registered entry ID')
    results=read_tsv('reports/data/corpus-results.tsv')
    measured={r['id']:r for r in results}
    if len(measured)!=len(results):
        raise SystemExit('Duplicate corpus result ID')
    classes=json.loads((DATA/'corpus-classification.json').read_text())
    bmap=json.loads((DATA/'bip-program-map.json').read_text())
    proposal_map=json.loads((DATA/'unnumbered-proposal-map.json').read_text())
    unclassified=set(meta)-set(classes)
    if unclassified:
        raise SystemExit('Unclassified registry IDs: '+', '.join(sorted(unclassified)))
    count_mismatch={i for i in set(meta)&set(measured) if meta[i]['vectors']!=measured[i]['vectors_total']}
    snapshot_stale=args.runner is None
    verified_fp=None
    budgets={}
    input_paths=list(INPUTS)
    if args.runner is not None:
        runner=args.runner.resolve()
        saved=DATA/'run-fingerprint.txt'
        current=subprocess.check_output([str(runner),'fingerprint'],cwd=ROOT,text=True).strip()
        if not saved.is_file() or not current or saved.read_text().strip()!=current:
            raise SystemExit('STALE: use the same frozen executable as the successful full corpus run')
        if set(meta)!=set(measured) or count_mismatch or any(r['vectors_ok']!=r['vectors_total'] for r in results):
            raise SystemExit('Incomplete registry/results or missing/failed vectors')
        exported=subprocess.check_output([str(runner),'metadata'],cwd=ROOT,text=True)
        if list(csv.DictReader(io.StringIO(exported),delimiter='\t'))!=metadata:
            raise SystemExit('Export current metadata from the verified frozen executable first')
        for r in read_tsv('reports/data/candidate-impact.tsv'):
            ident=r['program']
            if ident not in measured or r['current_mwu']!=measured[ident]['cost_mwu']:
                raise SystemExit('Impact original bound disagrees: '+ident)
            budget=(int(r['assumed_budget_wu']),r['feasibility_applicable'])
            if ident in budgets and budgets[ident]!=budget:
                raise SystemExit('Impact budget disagreement: '+ident)
            budgets[ident]=budget
        if set(budgets)!=set(meta):
            raise SystemExit('Missing verified budget evidence')
        for ident in meta:
            is_client=classes[ident].get('execution_context')=='client_mode'
            if (measured[ident]['execution_context']=='client-verifier')!=is_client or (budgets[ident][1]=='false')!=is_client:
                raise SystemExit('Client context disagreement: '+ident)
        verified_fp=current
        input_paths+=['reports/data/run-fingerprint.txt','reports/data/candidate-impact.tsv']

    def fixed_budget(ids):
        if not ids or not budgets:
            return '—'
        def fit(i):
            budget,applicable=budgets[i]
            if applicable=='false':
                return i+': n/a (client)'
            before=int(measured[i]['cost_mwu'])<=1000*budget
            after=int(measured[i]['whatif_mwu'])<=1000*budget
            return i+': '+('yes' if before else 'no')+' / '+('yes' if after else 'no')+' at '+str(budget)+' WU'
        return '; '.join(map(fit,ids))

    def costs(ids):
        c=[];e=[];v=[];statuses=[]
        for i in ids:
            r=measured.get(i)
            if i not in meta:
                c.append(i+': UNREGISTERED');e.append(i+': —');v.append(i+': —');statuses.append('UNREGISTERED')
            elif not r or snapshot_stale:
                c.append(i+': PENDING');e.append(i+': PENDING');v.append(i+': PENDING');statuses.append('PENDING')
            else:
                label='MEASURED'
                c.append(i+': '+wu(r['cost_mwu']))
                e.append(i+': '+wu(r['whatif_mwu']))
                v.append(i+': '+r['vectors_ok']+'/'+r['vectors_total']+(' vs current '+meta[i]['vectors'] if i in count_mismatch else ''))
                statuses.append(label+(' / VECTOR_COUNT_CHANGED' if i in count_mismatch else '')+(' / FAIL' if r['vectors_ok']!=r['vectors_total'] else ''))
        return '; '.join(c) or '—','; '.join(e) or '—','; '.join(v) or '—','; '.join(sorted(set(statuses))) or 'NO_IMPLEMENTATION'
    def classification(i):
        return classes[i]['kind']
    counts=collections.Counter(classification(i) for i in meta)
    groups={classes[i]['count_group'] for i in meta}
    fullgroups={classes[i]['count_group'] for i in meta if classification(i).startswith('full_')}
    passing=[i for i,r in measured.items() if i in meta and r['vectors_ok']==r['vectors_total']]
    qualified_groups=None if snapshot_stale else {classes[i]['count_group'] for i in passing}
    qualification=('0 groups credited from this stale runner snapshot; no historical pass is credited to changed source. Current vector-only diagnostic passes remain separate evidence, linked in the witness-binding audit.' if qualified_groups is None else
                   f'{len(qualified_groups)} distinct counting groups have current passing vectors; {max(0,150-len(qualified_groups))} more are required to reach150. Failed or missing rows receive no credit.')
    lines=['# Corpus coverage and source-by-source costs','','Generated by `python3 tools/coverage_report.py` from the complete registered metadata export and saved source inventories. Every requested source row is retained; a proxy association is explicitly labeled and is never a port of the named protocol. WU uses the in-tree runner. The overlay column is always **ESTIMATE**, even when the original expression cost is measured.','','## Coverage and freshness','',f'Registered entries: **{len(meta)}**. Counting groups after explicit variant merges: **{len(groups)}**. Full bounded spend/verifier groups: **{len(fullgroups)}**. The raw gap to150 is {max(0,150-len(meta))}; the conservative distinct-group gap is **{max(0,150-len(groups))}**. Neither backlog rows nor source protocols count as programs.','','Classification means complete within the stated leaf/verifier interface and bounds, not a complete deployed protocol or a consensus safety audit. Kernels and protocol components remain in the inventory but do not masquerade as full applications. The CSFS and HTLC variants, two P2MR construction variants, and SHRINCS/SLH-DSA stateless reference profiles each share their corresponding group.','',table(['class','registered rows'],sorted(counts.items())),'',f'Runner artifact has {len(measured)} rows; {len(passing)} recorded passing rows intersect the current registry. Missing current IDs: {len(set(meta)-set(measured))}; obsolete result IDs: {len(set(measured)-set(meta))}; changed vector counts: {len(count_mismatch)}. **Snapshot status: '+('UNVERIFIED / FULL RE-RUN REQUIRED**.' if snapshot_stale else 'VERIFIED FULL-RUN FINGERPRINT `'+verified_fp+'`**.'),'','PENDING means no verified current measurement is shown. After a successful full run, regenerate metadata and this report using the same frozen executable. Source hashes below pin the inputs to this join.','','## Every registered program','']
    lines += ['', 'Test-qualified goal count: '+qualification, 'The full-scope classification above describes the implemented interface; it does not certify a verifier whose current vectors have not passed.', '']
    if snapshot_stale:
        lines += ['All old runner costs are historical. Some prior expressions had witness-binding or canonical-encoding defects; their passing honest vectors did not establish a correct verifier. These costs must not be attributed to the repaired programs. Current vector-only evidence is recorded separately in [WITNESS-BINDING-AUDIT.md](WITNESS-BINDING-AUDIT.md).', '']
    retired=sorted(set(measured)-set(meta))
    if retired:
        lines += ['### Retired historical IDs — no program-count credit','',
                  ', '.join('`'+i+'`' for i in retired), '',
                  'The retired FRI fragment is not the full STARK verifier and is not counted alongside its replacement.','','### Current registered rows','']
    inventory=[]
    modulefiles=[p for directory in ['Corpus','Lib'] for p in (ROOT/'src/JetDiscovery'/directory).glob('*.hs')]
    expansion=ROOT/'src/JetDiscovery/Corpus/BitcoinExpansion.hs'
    expansion_text=expansion.read_text()
    for i,r in meta.items():
        c,e,v,status=costs([i]);cl=classes[i]
        origins=[str(p.relative_to(ROOT)) for p in modulefiles if '"'+i+'"' in p.read_text()]
        # BitcoinExpansion's reviewed constructor prefixes each App slug with
        # app-. Other modules must contain the exact complete identifier.
        if not origins and i.startswith('app-') and 'App "'+i[4:]+'"' in expansion_text:
            origins=[str(expansion.relative_to(ROOT))]
        if not origins:
            raise SystemExit('No source module for registered entry: '+i)
        row=dict(r,kind=cl['kind'],count_group=cl['count_group'],classification_note=cl['note'],source_modules='; '.join(origins),recorded_cost_wu=c,overlay_estimate_wu=e,recorded_vectors=v,measurement_status=status)
        inventory.append(row)
    with (DATA/'corpus-coverage.tsv').open('w') as out:
        wr=csv.DictWriter(out,list(inventory[0]),delimiter='\t',lineterminator='\n');wr.writeheader();wr.writerows(inventory)
    lines += [table(['program / class / group','published target and exact scope','recorded cost WU','overlay WU ESTIMATE','vectors / status'],[(f"`{r['id']}`; {r['kind']}; group `{r['count_group']}`",r['title']+'; '+r['classification_note']+' Assumptions: '+r['assumptions'],r['recorded_cost_wu'],r['overlay_estimate_wu'],r['recorded_vectors']+'; '+r['measurement_status']) for r in inventory]),'','The machine-readable [corpus-coverage.tsv](data/corpus-coverage.tsv) also retains every specification, vector source, source module and declared assumption.','','## All24 open softfork BIPs','']
    bips=[r for r in read_tsv('vendor-specs/bip-inventory/softfork-triage.tsv') if r['status'] not in ['Closed','Deployed']]
    if len(bips)!=24:
        raise SystemExit(f'Expected pinned24-row BIP inventory, got{len(bips)}; review mappings before regeneration')
    if {r['number'] for r in bips}!=set(bmap):
        raise SystemExit('Open BIP map must account for all and only the pinned open rows')
    if len(proposal_map)!=10 or len({r['id'] for r in proposal_map})!=len(proposal_map):
        raise SystemExit('Numberless proposal map does not cover the ten audited families')
    joined=[]
    header=['proposal / status','verdict and association / program IDs','native WU','combined overlay WU ESTIMATE','vectors / status','hypothetical fit before / after','exact scope gap']

    def proposal_row(dataset,key,title,status,source,m):
        ids=m['programs']
        if any(i not in meta for i in ids):
            raise SystemExit('Unknown corpus ID in proposal map: '+key)
        c,e,v,st=costs(ids)
        joined.append(dict(source_set=dataset,source_key=key,source_name=title,source_metric=status,source_url=source,execution_identity='',execution_role='',execution_source='',source_review_verdict=m['verdict'],source_review_reason='',association=m['association'],programs='; '.join(ids),recorded_cost_wu=c,overlay_estimate_wu=e,recorded_vectors=v,measurement_status=st,exact_gap=m['gap']))
        return [f'[{title}]({source}); {status}',m['verdict']+'; '+m['association']+'; '+', '.join(ids),c,e,v+'; '+st,fixed_budget(ids),m['gap']]

    bip_rows=[proposal_row('open-bip',r['number'],'BIP '+r['number']+': '+r['title'],r['status'],r['source'],bmap[r['number']]) for r in bips]
    no_number_rows=[proposal_row('unnumbered-proposal',m['id'],m['title'],'unnumbered',m['source'],m) for m in proposal_map]
    proposal_sections=['## All 24 open softfork BIPs','',
        'Costs attach to the exact corpus IDs. The optional fit column compares native and combined overlay bounds at the same first-vector witness-bytes + 50 WU scenario; it is not a Bitcoin consensus budget rule. Scope gaps do not imply a new jet is necessary.','',
        table(header,bip_rows),'','## Ten audited unnumbered proposal families','',
        'This is the documented search scope in [BIP-INVENTORY.md](BIP-INVENTORY.md). The BIP index and these proposal searches have different coverage.','',table(header,no_number_rows)]
    lines += proposal_sections + ['','## Every ranked protocol and execution-source row','','TVL includes BOTH complete saved top20 sets for each chain: all categories including custodial holdings, and the separately filtered non-CEX ranking. Their source_set values are distinct; overlapping protocols are not merged or counted as additional applications. Gas and compute tables cover **all rows** of the complete one-block source TSVs, including unknown implementations and non-contract recipients. They do not replace unavailable Etherscan/Solscan period rankings. Source period/coverage limits remain those documented in [contract-inventory.md](contract-inventory.md). Architectural PROXY costs belong to the named corpus programs, not to the source contract itself.']
    lines += ['', 'The separate [Soltop period supplement](PERIOD-RANKINGS.md) adds all 20 provider-reported last-24h rows captured on 2026-11-05 at 08:23:43 UTC. Its exact ranking cutoffs, ingestion completeness, nested-CPI and failed-transaction accounting are unknown; do not call these exclusive CU or combine them numerically with the one-slot exclusive-CU sample. This is not a recovered Solscan top100 or Ethereum period ranking. All four provider metrics retain full source precision below. Unknown implementations remain explicit gaps.']
    datasets=[('protocol-tvl','reports/data/protocol-ranking.tsv'),('protocol-tvl-non-cex','reports/data/protocol-ranking-non-cex.tsv'),('ethereum-gas','reports/data/ethereum-gas-ranking.tsv'),('solana-compute','reports/data/solana-compute-ranking.tsv'),('solana-24h-soltop',PERIOD_DIR+'/top20.tsv')]
    execution_joins={(r['chain'],r['slug']):r for r in read_tsv('reports/data/protocol-ranking-non-cex.tsv') if r.get('verified_execution_id')}
    for dataset,path in datasets:
        source=read_tsv(path);rows=[]
        if dataset=='solana-24h-soltop':
            triage={r['program_id']:r for r in read_tsv(PERIOD_DIR+'/utxo-triage.tsv')}
            if len(source)!=20 or len(triage)!=20 or {r['program_id'] for r in source}!=set(triage):
                raise SystemExit('Soltop20-row metric/identity inventory mismatch')
            source=[dict(r,**{k:v for k,v in triage[r['program_id']].items() if k not in r}) for r in source]
        for r in source:
            ids,assoc,gap=classify_contract(dataset,r)
            identity='';role='';execution_source=''
            source_verdict=r.get('verdict',r.get('utxo_verdict',''))
            source_reason=r.get('reason',r.get('utxo_verdict_reason',r.get('utxo_verdict','')))
            if dataset in ['protocol-tvl','protocol-tvl-non-cex']:
                key=r['chain']+':'+r['slug'];name=r['chain']+' #'+r['rank']+' '+r['name'];metric=r.get('chain_value_usd',r.get('chain_tvl_usd','UNKNOWN'))+' USD';url='https://defillama.com/protocol/'+r['slug']
                evidence_row=execution_joins.get((r['chain'],r['slug']),r)
                identity=evidence_row.get('verified_execution_id','');role=evidence_row.get('execution_role','not joined');execution_source=evidence_row.get('execution_source','')
            elif dataset=='ethereum-gas':
                key=r['recipient'];name='#'+r['rank_all_recipients']+' '+r['label']+' '+key;metric=r['gas_used']+' gas / '+r['transactions']+' tx; code='+r['has_execution_code'];url='https://etherscan.io/address/'+key
                identity=key;role='sampled transaction recipient'
            elif dataset=='solana-compute':
                key=r['program'];name='#'+r['rank']+' '+r['label']+' '+key;metric=r['exclusive_logged_cu']+' exclusive logged CU / '+r['logged_invocations']+' calls';url='https://solscan.io/account/'+key
                identity=key;role='program in sampled execution logs'
            else:
                key=r['program_id'];name='#'+r['rank']+' '+r['label']+' '+key
                metric=r['total_cu_consumed']+' provider24h CU / count='+r['transaction_count']+' / average CU='+r['avg_cu_per_transaction']+' / success%='+r['success_rate']
                url='https://api.soltop.sh/api/top-programs';identity=key;role='provider-ranked program; source implementation '+('unclassified' if r['label'].startswith('Unclassified') else 'label retained')
            evidence=(identity+'; '+role if identity else 'Not joined')+(f'; [identity source]({execution_source})' if execution_source else '')
            if source_reason:
                gap+=' Source review: '+source_reason
            c,e,v,st=costs(ids)
            rows.append([f'[{name}]({url})',metric,evidence,assoc+'; '+', '.join(ids),c,e,v+'; '+st,gap])
            joined.append(dict(source_set=dataset,source_key=key,source_name=name,source_metric=metric,source_url=url,execution_identity=identity,execution_role=role,execution_source=execution_source,source_review_verdict=source_verdict,source_review_reason=source_reason,association=assoc,programs='; '.join(ids),recorded_cost_wu=c,overlay_estimate_wu=e,recorded_vectors=v,measurement_status=st,exact_gap=gap))
        lines+=['',f'### {dataset}: all{len(source)} rows','',table(['named source','source metric','execution identity / source join','association / program IDs','recorded cost WU','overlay WU ESTIMATE','vectors / status','exact gap'],rows)]
    with (DATA/'source-cost-coverage.tsv').open('w') as out:
        wr=csv.DictWriter(out,list(joined[0]),delimiter='\t',lineterminator='\n');wr.writeheader();wr.writerows(joined)
    backlog=read_tsv('reports/data/growth-backlog.tsv')
    new=[r for r in backlog if r['count_policy']=='prospective_new']
    upgrades=[r for r in backlog if r['count_policy']!='prospective_new']
    lines+=['','## Growth backlog and counting gate','',f'The conservative gap is {max(0,150-len(groups))} additional distinct groups. The backlog below contains {len(new)} prospective new scopes and {len(upgrades)} upgrades/alternatives that receive no extra counting credit. A source-backed target is not yet an independently validated implementation: full-text/contract review must establish its exact predicate, Bitcoin enforcement path and distinction from existing groups before coding and counting it. If two rows reduce to the same program modulo constants, thresholds or tree depth, merge them. Parameter sweeps remain measurements within one group.','','Each accepted new row must supply a full bounded spend predicate or verifier, independent/ upstream vectors including rejection cases, actual jet-substituted WU measurement, and the complete publication/spec provenance. Source-backed candidates whose deployment path depends on unexposed chain context must retain that gap instead of using witness data as an oracle.','',table(['target / count policy','primary specification','distinct work to implement / gate'],[(r['id']+'; '+r['count_policy'],f"[{r['source_title']}]({r['source_url']})",r['target']+'; '+r['count_gate']) for r in backlog]),'','## Input provenance','','Reproduce after building and successfully running the current full corpus:','','```sh','<same-frozen-runner> metadata > reports/data/corpus-metadata.tsv','python3 tools/coverage_report.py --runner <same-frozen-runner>','```','','[source-cost-coverage.tsv](data/source-cost-coverage.tsv) is the complete machine-readable source join. No cost is fabricated for an unimplemented or unmapped source.','','| input | SHA-256 |','| --- | --- |']
    provenance={}
    for path in input_paths:
        digest=hashlib.sha256((ROOT/path).read_bytes()).hexdigest();provenance[path]=digest;lines.append(f'| `{path}` | `{digest}` |')
    (DATA/'coverage-input-hashes.json').write_text(json.dumps(provenance,indent=2)+'\n')
    (ROOT/'reports/bip-verdicts.md').write_text('\n'.join(['# Script-extension verdicts','']+proposal_sections)+'\n')
    (ROOT/'reports/coverage-and-costs.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps(dict(registered=len(meta),counting_groups=len(groups),full_groups=len(fullgroups),classes=counts,measurement_stale=snapshot_stale,missing_measurements=len(set(meta)-set(measured)),source_rows=len(joined),backlog_new=len(new),backlog_upgrades=len(upgrades)),indent=2))

if __name__=='__main__':
    main()
