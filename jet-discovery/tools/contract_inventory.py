#!/usr/bin/env python3
"""Rebuild bounded complete ranked tables from vendored, never-executed data."""
import collections,csv,datetime,hashlib,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[1];data=root/'vendor-specs/contracts';out=root/'reports/data'
protocols=json.loads((data/'defillama-protocols.json').read_text())

def map_protocol(x):
 c=x.get('category','')
 if c=='CEX':return 'Not applicable as a contract','Custodial balances are demand for ownership/reserve proofs, not an enforceable UTXO state transition.'
 if c in ['Liquid Staking','Restaking','Staking Pool']:return 'Partial fit: staking custody/unbonding','Bitcoin can enforce authorization, CSV and slash payouts; foreign validator selection, rewards and consensus need external attestations.'
 if c in ['Lending','CDP']:return 'Partial fit: oracle-authorized lending covenant','Native collateral, a signed price and bounded liquidation payouts fit; current oracle freshness, external debt/token state and the complete foreign lending ledger are not established.'
 if 'Bridge' in c:return 'Partial fit: authenticated bridge messages','Guardian signatures or a source-chain proof plus a replay-protected output state can authorize withdrawal; source-chain finality is external.'
 if c=='Dexs':return 'Partial fit: reserve-state transition','AMM arithmetic and output allocation fit covenants; multiple assets need an explicit representation and serialized pool state.'
 if c in ['Derivatives','Perpetuals']:return 'Partial fit: signed collateral settlement','A committed native collateral position and signed index support payout arithmetic; latest funding periods, oracle freshness, margin and global exchange state need additional authenticated data/state.'
 if c=='Basis Trading':return 'Partial fit: custody and attestations','On-chain collateral and ownership checks fit; exchange hedge positions and solvency remain attested off chain.'
 if c=='Risk Curators':return 'Not a standalone spending application','Portfolio allocation/permissions need a specified vault transition; the curator dashboard alone supplies no enforceable spend predicate.'
 if c=='RWA':return 'Partial fit: attested custody claim','An issuer/oracle authorizes redemption; external asset title and cash flows cannot be verified by Bitcoin alone.'
 return 'Unclassified: source implementation needed','Category alone does not establish a correct Bitcoin state transition; no demand claim is inferred.'

lines=['# Data-ranked Ethereum and Solana demand inventory','','Snapshot retrieval: 2026-11-04 America/Los_Angeles (UTC data timestamps below). The first set is the complete top 20 entries for **each chain** after sorting every entry in the saved DefiLlama `/protocols` response by its numeric `chainTvls[chain]`. This intentionally retains CEX holdings, liquid staking, bridges and other categories rather than silently substituting DefiLlama\'s default DeFi-only filter. Parent/child protocols can overlap; TVL is a demand signal, not an additive corpus weight.','','The gas/compute sources are separate, explicitly bounded one-block snapshots. They are **not** a 24-hour popularity ranking. Etherscan Gas Tracker and Solscan Fee Tracker returned HTTP403 both through ordinary and escalated HTTP. Browser Harness failed to start and the in-app browser was unavailable. These explorer-period rankings therefore remain an access gap. The independently fetched complete blocks below add real data without filling that gap by assumption.','','Sources: [DefiLlama API](https://api.llama.fi/protocols), [Ethereum JSON-RPC](https://ethereum.org/en/developers/docs/apis/json-rpc/), [Solana getBlock](https://solana.com/docs/rpc/http/getblock), [Etherscan Gas Tracker](https://etherscan.io/gastracker), [Solscan Fee Tracker](https://solscan.io/analysis/fee-tracker). Raw responses and provenance are in `vendor-specs/contracts/`. UTXO mappings are architectural assessments from protocol categories and explicit source paths, not claims that these foreign protocols currently run on Bitcoin. Rebuild: `python3 tools/contract_inventory.py`.','']
prows=[]
for chain in ['Ethereum','Solana']:
 eligible=[x for x in protocols if isinstance(x.get('chainTvls',{}).get(chain),(int,float))]
 ranked=sorted(eligible,key=lambda x:(-x['chainTvls'][chain],x['slug']))[:20]
 lines+=['## '+chain+' protocol holdings / TVL','','Inspected all '+str(len(protocols))+' source records; '+str(len(eligible))+' have a numeric value for this chain. Every top-20 row is included below.','','| rank | protocol | category | chain value USD | UTXO verdict | reason |','| ---: | --- | --- | ---: | --- | --- |']
 for rank,x in enumerate(ranked,1):
  verdict,reason=map_protocol(x);v=x['chainTvls'][chain]
  lines.append(f'| {rank} | [{x["name"]}](https://defillama.com/protocol/{x["slug"]}) | {x.get("category","")} | {v:,.2f} | {verdict} | {reason} |')
  prows.append([chain,rank,x['name'],x['slug'],x.get('category',''),format(v,'.8f'),verdict,reason])
 lines+=['']
with (out/'protocol-ranking.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['chain','rank','name','slug','category','chain_value_usd','verdict','reason']);w.writerows(prows)

# Preserve the all-category holdings ranking above and add an explicit non-CEX
# protocol ranking. This does not pretend to match DefiLlama's optional UI flags.
verified={
 'lido':('0xae7ab96520DE3A18E5e111B5EaAb095312D7fE84','Lido/stETH staking proxy','https://docs.lido.fi/deployed-contracts/'),
 'aave-v3':('0x87870Bca3F3fD6335C3F4ce8392D69350B4fA4E2','Ethereum lending Pool proxy','https://github.com/bgd-labs/aave-address-book/blob/main/src/AaveV3Ethereum.sol'),
 'morpho-blue':('0xBBBBBbbBBb9cC5e90e3b3Af64bdAF62C37EEFFCb','Morpho singleton','https://docs.morpho.org/developers/contracts/addresses/'),
 'raydium-amm':('675kPX9MHTjS2zt1qfr1NYHuzeLXfQM9H24wFSUt1Mp8','AMMv4 program','https://github.com/raydium-io/raydium-docs-v1/blob/main/reference/program-addresses.mdx'),
 'kamino-lend':('KLend2g3cP87fffoy8q1mQqGKjrxjC8boSyAYavgmjD','KLend mainnet program','https://github.com/Kamino-Finance/klend-sdk/blob/master/README_KAMINO_MANAGER.md'),
 'jito-liquid-staking':('SPoo1Ku8WFXoNDMHPsrGSTSG1Y47rzgn41SLUNakuHy','SPL Stake Pool program (shared; pool account Jito4APyf642JPZPx3hGc6WWJ8zPKtRbRs4P815Awbb)','https://www.jito.network/docs/jitosol/jitosol-liquid-staking/security/deployed-programs/'),
 'pumpswap':('pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA','Pump AMM program','https://github.com/pump-fun/pump-public-docs/blob/main/idl/pump_amm.ts'),
 'orca-dex':('whirLbMiicVdio4qvUfM5KAg6Ct8VwpYzGff3uctyCc','Whirlpool program','https://github.com/orca-so/whirlpools')}
non_cex_rows=[]
for chain in ['Ethereum','Solana']:
 eligible=[x for x in protocols if isinstance(x.get('chainTvls',{}).get(chain),(int,float)) and x.get('category')!='CEX']
 ranked=sorted(eligible,key=lambda x:(-x['chainTvls'][chain],x['slug']))[:20]
 lines+=['## '+chain+' non-CEX protocol TVL top20','','Filter: remove exactly category`CEX`; retain liquid staking, bridges, restaking and curators. '+str(len(eligible))+' eligible source entries were ranked. Values are chain-specific adapter-reported USD, not the total across all chains. This is a separate list; the all-category list remains above. Operational deployment IDs below are verified representatives, not an assertion that one address accounts for all TVL. Source`address` fields in DefiLlama often identify governance tokens and are therefore not substituted for execution contracts. Missing joins remain explicit.','','| rank | protocol / source ID | category | chain TVL USD | operational contract / program (role) | UTXO verdict / reason |','| ---: | --- | --- | ---: | --- | --- |']
 for rank,x in enumerate(ranked,1):
  verdict,reason=map_protocol(x);v=x['chainTvls'][chain];deployment=verified.get(x['slug'])
  if deployment:
   address,role,url=deployment;execution=f'[`{address}`]({url}) ({role})'
  else:address='';role='not joined';url='';execution='Not joined: source protocol aggregates contracts/accounts; adapter`'+str(x.get('module','unknown'))+'` identifies the next source to inspect.'
  lines.append(f'| {rank} | [{x["name"]}](https://defillama.com/protocol/{x["slug"]}) / `{x.get("id","")}` | {x.get("category","")} | {v:,.2f} | {execution} | {verdict}: {reason} |')
  non_cex_rows.append([chain,rank,x['name'],x['slug'],x.get('id',''),x.get('category',''),format(v,'.8f'),x.get('module',''),address,role,url,verdict,reason])
 lines+=['']
with (out/'protocol-ranking-non-cex.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['chain','rank','name','slug','source_id','category','chain_tvl_usd','adapter_module','verified_execution_id','execution_role','execution_source','verdict','reason']);w.writerows(non_cex_rows)

b=json.loads((data/'ethereum-latest-block.json').read_text())['result'];rs=json.loads((data/'ethereum-block-receipts.json').read_text())['result']
assert len(rs)==len(b['transactions']) and {x['transactionHash'] for x in rs}=={x['hash'] for x in b['transactions']}
gas=collections.Counter();n=collections.Counter();selectors=collections.defaultdict(set)
for r in rs:
 assert r['blockHash']==b['hash'];a=r['to'] or r['contractAddress'] or 'creation';gas[a]+=int(r['gasUsed'],16);n[a]+=1
for t in b['transactions']:selectors[t['to'] or 'creation'].add(t['input'][:10])
assert sum(gas.values())==int(b['gasUsed'],16)
known={'0xdac17f958d2ee523a2206206994597c13d831ec7':('USDT','Token authorization/transfer maps to signed output assignment; issuer controls and ERC20 storage are external.'),'0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48':('USDC','Token authorization/transfer maps to signed output assignment; issuer controls and ERC20 storage are external.'),'0xe592427a0aece92de3edee1f18e0157c05861564':('Uniswap v3 SwapRouter','AMM reserve/tick arithmetic fits a serialized pool UTXO; arbitrary calls and native ERC20 balances do not.'),'0x68b3465833fb72a70ecdf485e0e4c7bd8665fc45':('Uniswap SwapRouter02','AMM reserve/tick arithmetic fits a serialized pool UTXO; multi-asset representation must be explicit.'),'0x66a9893cc07d91d95644aedd05d03f95e1dba8af':('Uniswap Universal Router','Individual signed orders and pool transitions fit; arbitrary command routing needs no distinct Bitcoin jet.'),'0x0000000071727de22e5e9d8baf0edac6f37da032':('ERC4337 EntryPoint v0.7','Signature/session/nonce policies fit a UTXO; account storage and general callback execution do not directly port.'),'0xca11bde05977b3631167028862be2a173976ca11':('Multicall3','Batched read/call routing is not itself a new cryptographic primitive; called contracts require separate classification.')}
codes={}
for batch in range(3):
 req=json.loads((data/f'ethereum-code-request-{batch}.json').read_text());res=json.loads((data/f'ethereum-code-response-{batch}.json').read_text())
 by_id={x['id']:x for x in res}
 for x in req:
  assert 'result' in by_id[x['id']],by_id[x['id']]
  codes[x['params'][0]]=by_id[x['id']]['result']
assert set(gas)==set(codes)
contract_count=sum(code!='0x' for code in codes.values())
lines+=['## Ethereum gas use: one complete block','','Block '+str(int(b['number'],16))+' (`'+b['hash']+'`), timestamp '+datetime.datetime.fromtimestamp(int(b['timestamp'],16),datetime.timezone.utc).isoformat()+'. Inspected all '+str(len(rs))+' receipts and transactions; total receipt gas '+str(sum(gas.values()))+' equals the header. Rank is sum of receipt `gasUsed` charged to the top-level recipient, **including reverted transactions and nested calls**. It is not attribution to each internal callee. All117 recipients were checked with `eth_getCode` at the same block; '+str(contract_count)+' have nonempty execution code (including delegated-code accounts). The top20 table includes only these; the TSV retains every recipient and code status. Known deployment labels are convenience metadata; unknown recipients remain explicitly unclassified.','','| rank | recipient | deployment label | gas used | transactions | UTXO verdict / reason |','| ---: | --- | --- | ---: | ---: | --- |']
erows=[]
contract_rank=0
for rank,(a,v) in enumerate(gas.most_common(),1):
 if codes[a]!='0x':contract_rank+=1
 label,reason=known.get(a,('Unclassified recipient','Unclassified: no verified implementation identified; receipt totals and input selectors alone cannot justify a UTXO mapping.'))
 erows.append([rank,contract_rank if codes[a]!='0x' else '',a,label,v,n[a],codes[a]!='0x',len(codes[a][2:])//2,','.join(sorted(selectors[a])),reason])
 if codes[a]!='0x' and contract_rank<=20:lines.append(f'| {contract_rank} | [`{a}`](https://etherscan.io/address/{a}) | {label} | {v:,} | {n[a]} | {reason} |')
with (out/'ethereum-gas-ranking.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['rank_all_recipients','rank_nonempty_code','recipient','label','gas_used','transactions','has_execution_code','code_bytes','input_selectors','utxo_verdict_reason']);w.writerows(erows)

b=json.loads((data/'solana-finalized-block.json').read_text())['result'];cu=collections.Counter();calls=collections.Counter();missing=0;truncated=0
for tx in b['transactions']:
 logs=tx['meta'].get('logMessages')
 if logs is None:missing+=1;continue
 stack=[]
 for line in logs:
  m=re.fullmatch(r'Program (\S+) invoke \[(\d+)\]',line)
  if m:stack.append([m.group(1),0]);continue
  m=re.fullmatch(r'Program (\S+) consumed (\d+) of (\d+) compute units',line)
  if m:
   name,value=m.group(1),int(m.group(2));assert stack and stack[-1][0]==name
   exclusive=value-stack[-1][1];assert exclusive>=0
   cu[name]+=exclusive;calls[name]+=1
   if len(stack)>1:stack[-2][1]+=value
   continue
  m=re.fullmatch(r'Program (\S+) (?:success|failed: .*)',line)
  if m and stack and stack[-1][0]==m.group(1):stack.pop()
 if stack:truncated+=1
observed=sum(cu.values());total=sum(tx['meta'].get('computeUnitsConsumed',0) for tx in b['transactions'])
solknown={'pfeeUxB6jkeY1Hxd7CsFCAjcbHA9rWtchMGdZ6VojVZ':('Pump fee program','Fee-rate calculation and multi-recipient payout splitting fit an output covenant; dynamic protocol configuration needs committed or authenticated state.'),'pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA':('PumpSwap AMM','Reserve-state AMM transition fits a covenant with explicit asset representation.'),'6EF8rrecthR5Dkzon8Nwu78hRvfCKubJ14M5uBEwF6P':('Pump.fun','Bonding-curve arithmetic and payout covenant fit; token mint/state representation must be specified.'),'ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL':('SPL Associated Token Account','Account-address derivation is specific to Solana; Bitcoin outputs already identify ownership. Not a direct application port.'),'TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb':('SPL Token-2022','Transfer authorization fits a UTXO; account extensions and token supply need explicit asset semantics.'),'whirLbMiicVdio4qvUfM5KAg6Ct8VwpYzGff3uctyCc':('Orca Whirlpool','Concentrated-liquidity tick arithmetic and per-position state fit a serialized pool UTXO.'),'cpamdpZCGKUy5JxQXB4dcpGPiikHawvSWAd6mEn1sGG':('Meteora DAMM v2','Reserve/invariant arithmetic and fee allocation fit a pool UTXO with explicit asset semantics.')}
lines+=['','## Solana compute use: one complete finalized block','','Slot465608975 (`'+b['blockhash']+'`), timestamp '+datetime.datetime.fromtimestamp(b['blockTime'],datetime.timezone.utc).isoformat()+'. Inspected all '+str(len(b['transactions']))+' transactions, '+str(missing)+' missing log arrays and '+str(truncated)+' unclosed invocation stacks. Rank uses exclusive compute from every `Program ... consumed` record, subtracting nested invocations to avoid double counting. Logged exclusive compute totals '+str(observed)+'; transaction metadata totals '+str(total)+'. The difference '+str(total-observed)+' is unassigned overhead/native work and is not allocated by guess. All logged programs are in the TSV. Current-block measurements are burst-sensitive.','','| rank | program | label | logged exclusive CU | invocations with CU logs | UTXO verdict / reason |','| ---: | --- | --- | ---: | ---: | --- |']
srows=[]
for rank,(a,v) in enumerate(cu.most_common(),1):
 label,reason=solknown.get(a,('Unclassified program','Unclassified: no verified program implementation identified; a public program ID and compute total do not determine an enforceable Bitcoin predicate.'))
 srows.append([rank,a,label,v,calls[a],reason])
 if rank<=20:lines.append(f'| {rank} | [`{a}`](https://solscan.io/account/{a}) | {label} | {v:,} | {calls[a]} | {reason} |')
with (out/'solana-compute-ranking.tsv').open('w') as f:
 w=csv.writer(f,delimiter='\t',lineterminator='\n');w.writerow(['rank','program','label','exclusive_logged_cu','logged_invocations','utxo_verdict_reason']);w.writerows(srows)
lines+=['','## Time and oracle semantics: exact scope, not foreign-state equivalence','','Bitcoin transaction `nLockTime` is a chosen lower bound on validity of the spend. If consensus accepts the transaction, the applicable chain height/time has reached that bound. The spender can choose an old bound. Checking`oracleTs <= txLockTime <= oracleTs +3600` therefore does **not** establish that a report is recent relative to the current chain tip or median time. No current-time primitive is invented here. The repository also does not provide an external Chainlink/Aave/Jupiter account-state root to authenticate their latest state.','','| program / pattern | conditions actually verified | condition not established / mapping verdict |','| --- | --- | --- |',
'| `ethsol-lending-liquidation` (existing Aave/Compound/Solend-style example) | Oracle signature, collateral/debt health inequality, payout, and signed timestamp compared with chosen transaction locktime | Partial/oracle-authorized native collateral policy. The one-hour locktime interval is not current-chain freshness. No claim of equivalence to latest Aave debt/oracle state. |',
'| `app-median-oracle-settlement` | Three fixed BIP340 signers authenticate one fixed32-byte context identifier and all three observations; median selects two committed payouts | A signed report consumer, not the complete Chainlink OCR protocol or latest feed state. There is no timestamp, dynamic round number, or proof that these are the newest observations. |',
'| `app-perpetual-funding-settlement` | Oracle signature on a fixed position-context ID plus new cumulative index; committed previous index/position, checked payout arithmetic, index bounds and CSV24 | One native collateral settlement path, not an exchange or a latest-period funding calculation. CSV delays spending this UTXO; it does not authenticate the age of the oracle index or a dynamic funding-period ID. |',
'| `xchain-eip712-permit` | Exact EIP712/ERC2612 signed digest, constant owner/domain, nonce7 and signature recovery | The signed deadline is authenticated but not enforced against current chain time. This is permit authorization, not the complete ERC20 allowance ledger or expiry behavior. |',
'| `app-hodl-price-vault` | Owner signature; oracle-signed height/price; minimum report height and price; transaction lockheight at least the report height | Establishes a qualifying signed report at/after a committed lower height, not the current price or report freshness. Such a report can remain usable later. |',
'| `ethsol-linear-vesting` and `ethsol-dutch-auction` | Monotone amount/price calculations evaluated at the chosen transaction lower bound | They can conservatively enforce maturity-dependent payout bounds: choosing an older bound cannot withdraw more future vesting or pay a cheaper future Dutch price early. They do not reveal the current chain clock or reproduce every foreign timestamp/account-state rule. |',
'| `app-refillable-withdrawal-budget` | Remaining allowance/nonce committed in state; refill requires CSV144 since the previous state output | Explicit idle-period bucket. It is not a wall-clock Safe AllowanceModule period; every new state output restarts the relative delay. |',
'',
'Upper-bound expiration/freshness requirements, including the motivation behind OP_EXPIRE, are an execution-environment/primitive and consensus-integration question. A faster hash, field or signature jet cannot manufacture the missing trusted current-time input. Signed timestamps/rounds could be added as an explicit oracle model, but their issuer and replay/freshness assumptions must then be stated; that is not silently done by these examples.',
'',
'Primary context: [Bitcoin BIP65/CLTV](https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki), [BIP68 relative locks](https://github.com/bitcoin/bips/blob/master/bip-0068.mediawiki), [Chainlink OCR](https://docs.chain.link/architecture-overview/off-chain-reporting), [dYdX funding](https://docs.dydx.xyz/concepts/trading/funding), [ERC2612](https://eips.ethereum.org/EIPS/eip-2612). The per-program assumptions and the in-tree Bitcoin timelock implementation determine what the corpus actually checks.']
lines+=['','## Corpus mapping and remaining coverage','','Implemented paths in `Corpus.ContractExpansion`: full secp256k1 ECDSA verification, Ethereum public-key recovery and address authorization, a bounded Keccak Merkle authentication path, EIP712/ERC2612 permit authorization and Wormhole guardian quorum when present in the generated corpus index. `Corpus.ContractMath` adds exact full-range Uniswap TickMath, Curve3pool Newton invariant evaluation with explicit convergence bound, and full-width mulDiv. `Corpus.FinancialApps` adds actual native-collateral funding settlement, authenticated median-report payout, fractional conditional collateral redemption, and royalty splitting. Existing `Corpus.EthSol` covers vesting, Dutch auctions, Safe allowances and oracle lending liquidation; `Corpus.DeFi` covers constant-product swap arithmetic. `Corpus.BitcoinExpansion` adds distinct complete bounded spend conditions with signed covenant-negative vectors.','','The target of150 programs is **not achieved by this inventory**. A protocol does not count as a program. Pendle exp/ln, full transferable conditional-token accounting and Squads proposal/state transitions remain explicit implementation gaps. A funding settlement is not an entire perpetual exchange, a Merkle path is not the complete Bubblegum compressed-NFT program, and the bounded Curve invariant is not the full pool. Only entries passing their vectors in the generated corpus index count as measured programs. The unclassified gas/compute recipients are additional source-analysis gaps; they are not treated as technically boring or inapplicable.','','## Label sources and licensing','','Deployment label references: [Uniswap addresses](https://docs.uniswap.org/contracts/v3/reference/deployments/ethereum-deployments), [Pump official IDL](https://github.com/pump-fun/pump-public-docs/blob/main/idl/pump_amm.ts), [SPL Associated Token Account](https://www.solana-program.com/docs/associated-token-account), [SPL Token2022](https://www.solana-program.com/docs/token-2022), [Orca Whirlpools](https://github.com/orca-so/whirlpools), [Meteora DAMMv2](https://docs.meteora.ag/developer-guides/damm-v2/typescript-sdk/example), [EntryPoint deployments](https://github.com/eth-infinitism/account-abstraction), [Multicall3 deployment list](https://www.multicall3.com/deployments). Unknown labels are deliberately retained as unknown. RPC snapshots are public on-chain facts; no software license is inferred from endpoint access. DefiLlama API data is stored as source data, with no new license grant inferred. Primary-source specification files are pinned and license evidence retained in `vendor-specs/contracts/spec-provenance.json`. Downloaded source is never imported, built or executed by the harness. Program vectors are independently derived and labeled accordingly.','']
(root/'reports/contract-inventory.md').write_text('\n'.join(lines))
manifest=[]
for p in sorted(data.iterdir()):
 if p.is_file() and p.name!='snapshot-hashes.json':manifest.append({'file':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(data/'snapshot-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('protocol rows',len(prows),'Ethereum recipient rows',len(erows),'Solana logged program rows',len(srows),'observed CU',observed,'metadata CU',total)
