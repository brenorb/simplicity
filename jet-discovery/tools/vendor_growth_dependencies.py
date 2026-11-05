#!/usr/bin/env python3
"""Retrieve selected imported source/spec dependencies as inert, hashed data."""
import concurrent.futures,datetime,hashlib,json,pathlib,urllib.request
ROOT=pathlib.Path(__file__).resolve().parents[1]/'vendor-specs'/'contract-growth'
PINS={p['repository']:p['revision'] for p in json.loads((ROOT/'revision-pins.json').read_text())}
SOURCES={
 'gnosis/conditional-tokens-contracts':['contracts/CTHelpers.sol'],
 'cowprotocol/contracts':['src/contracts/libraries/GPv2Order.sol','src/contracts/libraries/GPv2Trade.sol','src/contracts/GPv2Signing.sol'],
 'compound-finance/compound-protocol':['contracts/ExponentialNoError.sol','contracts/InterestRateModel.sol','contracts/JumpRateModelV2.sol','contracts/BaseJumpRateModelV2.sol','contracts/Comptroller.sol'],
 'smartcontractkit/libocr':['contract2/OCR2Abstract.sol'],
 'balancer/balancer-v2-monorepo':['pkg/solidity-utils/contracts/math/FixedPoint.sol','pkg/solidity-utils/contracts/math/Math.sol'],
 'DODOEX/contractV2':['contracts/lib/DecimalMath.sol','contracts/lib/SafeMath.sol'],
 'Uniswap/v3-core':['contracts/libraries/TickMath.sol','contracts/libraries/Tick.sol','contracts/libraries/TickBitmap.sol','contracts/libraries/Position.sol','contracts/libraries/Oracle.sol','contracts/libraries/FullMath.sol','contracts/libraries/SqrtPriceMath.sol','contracts/libraries/LiquidityMath.sol','contracts/libraries/SafeCast.sol','contracts/libraries/BitMath.sol','contracts/libraries/FixedPoint96.sol','contracts/libraries/FixedPoint128.sol','contracts/libraries/UnsafeMath.sol','contracts/libraries/LowGasSafeMath.sol'],
 'pendle-finance/pendle-core-v2-public':['contracts/core/libraries/math/PMath.sol','contracts/core/StandardizedYield/PYIndex.sol','contracts/core/libraries/math/PYIndex.sol','contracts/core/libraries/MiniHelpers.sol','contracts/core/libraries/Errors.sol'],
 'gnosis/conditional-tokens-market-makers':['contracts/MarketMaker.sol','contracts/ConstructedCloneFactory.sol'],
}
def save(item):
 repo,path=item;revision=PINS[repo];url=f'https://raw.githubusercontent.com/{repo}/{revision}/{path}'
 row=dict(repository=repo,path=path,revision=revision,source_url=url,retrieved_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'jet-discovery-inert-source-inventory'})
  raw=urllib.request.urlopen(req,timeout=45).read();name=repo.replace('/','_')+'_'+path.replace('/','_');(ROOT/name).write_bytes(raw)
  row.update(local_file=name,sha256=hashlib.sha256(raw).hexdigest(),status='saved as data; never executed')
  provenance=json.loads((ROOT/'provenance.json').read_text());parent=next(r for r in provenance if r['repository']==repo)
  row['license']=next((l.split('SPDX-License-Identifier:',1)[1].strip() for l in raw.decode(errors='replace').splitlines() if 'SPDX-License-Identifier:' in l),parent.get('license','No grant inferred'))
  for key in ['license_file','license_sha256']:
   if key in parent:row[key]=parent[key]
 except Exception as e:row.update(status='access gap',error=str(e))
 return row
def main():
 items=[(r,p) for r,paths in SOURCES.items() for p in paths]
 with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(save,items))
 (ROOT/'dependency-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
 for r in rows: print(r['status'],r['repository'],r['path'],r.get('error',''))
if __name__=='__main__':main()
