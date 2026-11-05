#!/usr/bin/env python3
"""Pin primary growth-scope sources as inert data. Never import downloaded code."""
import concurrent.futures,datetime,hashlib,json,pathlib,urllib.request

OUT=pathlib.Path(__file__).resolve().parents[1]/'vendor-specs'/'contract-growth'
SOURCES=[
 ('ethereum/ercs','master',['ERCS/erc-4626.md','ERCS/erc-7540.md']),
 ('argotorg/solidity','develop',['docs/examples/blind-auction.rst']),
 ('balancer/balancer-v2-monorepo','master',['pkg/pool-weighted/contracts/WeightedMath.sol','pkg/solidity-utils/contracts/math/LogExpMath.sol']),
 ('curvefi/twocrypto-ng','main',['contracts/main/TwocryptoMath.vy','contracts/main/Twocrypto.vy']),
 ('DODOEX/contractV2','main',['contracts/lib/PMMPricing.sol','contracts/lib/DODOMath.sol']),
 ('pendle-finance/pendle-core-v2-public','main',['contracts/core/libraries/math/LogExpMath.sol','contracts/core/Market/MarketMathCore.sol']),
 ('Uniswap/v3-core','main',['contracts/UniswapV3Pool.sol','contracts/libraries/SwapMath.sol']),
 ('compound-finance/compound-protocol','master',['contracts/CToken.sol']),
 ('smartcontractkit/libocr','master',['contract2/OCR2Aggregator.sol']),
 ('wormhole-foundation/wormhole','main',['ethereum/contracts/bridge/Bridge.sol','ethereum/contracts/Messages.sol']),
 ('Squads-Protocol/v4','main',['programs/squads_multisig_program/src/instructions/proposal_create.rs','programs/squads_multisig_program/src/instructions/proposal_vote.rs','programs/squads_multisig_program/src/instructions/vault_transaction_execute.rs','programs/squads_multisig_program/src/state/proposal.rs','programs/squads_multisig_program/src/state/multisig.rs']),
 ('metaplex-foundation/mpl-bubblegum','main',['programs/bubblegum/program/src/processor/transfer.rs','programs/bubblegum/program/src/state/leaf_schema.rs']),
 ('gnosis/conditional-tokens-contracts','master',['contracts/ConditionalTokens.sol']),
 ('cowprotocol/contracts','main',['src/contracts/GPv2Settlement.sol','src/contracts/libraries/GPv2Trade.sol']),
 ('Uniswap/permit2','main',['src/SignatureTransfer.sol','src/libraries/PermitHash.sol']),
 ('gnosis/conditional-tokens-market-makers','master',['contracts/LMSRMarketMaker.sol']),
]

def get(url):
 req=urllib.request.Request(url,headers={'User-Agent':'jet-discovery-primary-source-data'})
 return urllib.request.urlopen(req,timeout=45).read()

def fetch_group(group):
 repo,branch,paths=group;now=datetime.datetime.now(datetime.timezone.utc).isoformat();rows=[]
 try:
  pins=json.loads((OUT/'revision-pins.json').read_text()) if (OUT/'revision-pins.json').exists() else []
  pin=next((p for p in pins if p['repository']==repo and p['branch']==branch),None)
  commit=pin['revision'] if pin else json.loads(get(f'https://api.github.com/repos/{repo}/commits/{branch}'))['sha']
  tree=None
  for requested in paths:
   row={'repository':repo,'requested_branch':branch,'requested_path':requested,'revision':commit,'retrieved_utc':now}
   try:
    path=requested
    if '/' not in path:
     discoveries=json.loads((OUT/'path-discovery.json').read_text()) if (OUT/'path-discovery.json').exists() else {}
     known=discoveries.get(repo)
     if known and known['revision']==commit and not known['truncated']:
      matches=known['matches'][requested]
     else:
      if tree is None:tree=json.loads(get(f'https://api.github.com/repos/{repo}/git/trees/{commit}?recursive=1'))
      if tree.get('truncated'):raise ValueError('repository tree truncated; cannot silently select a sample')
      matches=[e['path'] for e in tree['tree'] if e['type']=='blob' and e['path'].split('/')[-1]==requested]
     if len(matches)!=1:raise ValueError(f'expected one exact basename, got {matches}')
     path=matches[0]
    url=f'https://raw.githubusercontent.com/{repo}/{commit}/{path}';raw=get(url)
    name=repo.replace('/','_')+'_'+path.replace('/','_');(OUT/name).write_bytes(raw)
    row.update(path=path,source_url=url,local_file=name,sha256=hashlib.sha256(raw).hexdigest(),status='saved as data, never executed')
    spdx=next((l.split('SPDX-License-Identifier:',1)[1].strip() for l in raw.decode(errors='replace').splitlines() if 'SPDX-License-Identifier:' in l),None)
    row['license']=spdx or 'See retained repository license; no additional grant inferred'
   except Exception as ex:row.update(status='access gap',error=str(ex))
   rows.append(row)
  for path in ['LICENSE','LICENSE.md','LICENSE.txt','COPYING']:
   try:
    raw=get(f'https://raw.githubusercontent.com/{repo}/{commit}/{path}')
    name=repo.replace('/','_')+'_'+path;(OUT/name).write_bytes(raw)
    for row in rows:row['license_file']=name;row['license_sha256']=hashlib.sha256(raw).hexdigest()
    break
   except Exception:pass
  else:
   for row in rows:
    if row.get('license','').startswith('See retained'):row['license']='No source SPDX/standard repository license retrieved; no grant inferred'
 except Exception as ex:rows=[{'repository':repo,'requested_branch':branch,'retrieved_utc':now,'status':'access gap','error':str(ex)}]
 return rows

def main():
 OUT.mkdir(parents=True,exist_ok=True)
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
  rows=[r for group in pool.map(fetch_group,SOURCES) for r in group]
 (OUT/'provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
 for r in rows:print(r['repository'],r.get('path',r.get('requested_path','')),r['status'],r.get('error',''))
 print(f"saved={sum(r['status'].startswith('saved') for r in rows)} gaps={sum(r['status']=='access gap' for r in rows)}")

if __name__=='__main__':main()
