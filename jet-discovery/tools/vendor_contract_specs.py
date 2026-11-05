#!/usr/bin/env python3
"""Retrieve public primary-source specs as data only; never import or execute them."""
import datetime,hashlib,json,pathlib,urllib.request
root=pathlib.Path(__file__).resolve().parents[1]/'vendor-specs'/'contracts'
sources=[('ethereum/EIPs','master','EIPS/eip-2612.md'),('ethereum/EIPs','master','EIPS/eip-712.md'),('lightning/bolts','master','03-transactions.md'),('JoinMarket-Org/joinmarket-clientserver','master','docs/fidelity-bonds.md'),('Uniswap/v3-core','main','contracts/libraries/TickMath.sol'),('Uniswap/v3-core','main','contracts/libraries/FullMath.sol'),('curvefi/curve-contract','master','contracts/pools/3pool/StableSwap3Pool.vy'),('gnosis/conditional-tokens-contracts','master','contracts/ConditionalTokens.sol'),('babylonlabs-io/btc-staking-ts','main','README.md'),('OpenZeppelin/openzeppelin-contracts','master','contracts/token/ERC20/extensions/ERC20Permit.sol')]
sources += [('lightning/bolts','master','README.md'),('bgd-labs/aave-address-book','main','src/AaveV3Ethereum.sol'),('pump-fun/pump-public-docs','main','idl/pump_amm.ts'),('pump-fun/pump-public-docs','main','idl/pump_fees.ts'),('Kamino-Finance/klend','master','programs/klend/src/lib.rs'),('ethereum/ercs','master','ERCS/erc-2612.md'),('ethereum/ercs','master','ERCS/erc-2981.md'),('babylonlabs-io/btc-staking-ts','main','src/staking/stakingScript.ts'),('wormhole-foundation/wormhole','main','ethereum/contracts/Messages.sol')]
existing=json.loads((root/'spec-provenance.json').read_text()) if (root/'spec-provenance.json').exists() else []
rows=[]
for repo,branch,path in sources:
 cached=next((r for r in existing if r.get('repository')==repo and r.get('path')==path and r.get('status','').startswith('saved') and (root/r['local_file']).exists()),None)
 if cached:
  assert hashlib.sha256((root/cached['local_file']).read_bytes()).hexdigest()==cached['sha256']
  rows.append(cached);continue
 row={'repository':repo,'branch_requested':branch,'path':path,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(f'https://api.github.com/repos/{repo}/commits/{branch}',headers={'User-Agent':'jet-discovery-research'})
  revision=json.load(urllib.request.urlopen(req,timeout=30))['sha']
  row['revision']=revision
  url=f'https://raw.githubusercontent.com/{repo}/{revision}/{path}';row['source_url']=url
  raw=urllib.request.urlopen(url,timeout=30).read()
  filename=repo.replace('/','_')+'_'+path.replace('/','_')
  (root/filename).write_bytes(raw);row['local_file']=filename;row['sha256']=hashlib.sha256(raw).hexdigest()
  row['license']='See source SPDX header, and repository LICENSE where retrievable; no additional license inferred'
  for license_path in ['LICENSE','LICENSE.md','LICENSE.txt']:
   try:
    lic=urllib.request.urlopen(f'https://raw.githubusercontent.com/{repo}/{revision}/{license_path}',timeout=20).read()
    licfile=repo.replace('/','_')+'_'+license_path
    (root/licfile).write_bytes(lic);row['license_file']=licfile;break
   except Exception: pass
  row['status']='saved as data, never executed'
 except Exception as e:row['status']='access gap';row['error']=str(e)
 rows.append(row)
for row in rows:
 if not row.get('local_file'): continue
 text=(root/row['local_file']).read_text(errors='replace')
 spdx=next((line.split('SPDX-License-Identifier:',1)[1].strip() for line in text.splitlines() if 'SPDX-License-Identifier:' in line),None)
 if spdx: row['license']=spdx
 elif row.get('license_file'):
  lic=(root/row['license_file']).read_text(errors='replace')
  if 'CC0 1.0 Universal' in lic: row['license']='CC0-1.0'
  elif 'Business Source License 1.1' in lic: row['license']='BUSL-1.1; file-specific overrides apply if present; see retained license for change date/terms'
  elif 'GNU LESSER GENERAL PUBLIC LICENSE' in lic: row['license']='LGPL-3.0; see retained LICENSE for exact grant'
  elif 'GNU GENERAL PUBLIC LICENSE' in lic: row['license']='GPL-3.0; see retained LICENSE for exact grant'
  elif 'Permission is hereby granted' in lic: row['license']='MIT'
  elif 'Apache License, Version 2.0' in lic: row['license']='Apache-2.0'
  else: row['license']='Custom repository license; see retained '+row['license_file']+'; not assumed permissive'
 elif row['repository']=='lightning/bolts':row['license']='CC-BY-4.0, as stated in repository README.md'
 else:row['license']='No license declaration found in inspected source or standard repository license paths; no grant inferred'
(root/'spec-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r.get(k) for k in ['repository','path','status','revision','error']} for r in rows],indent=2))
