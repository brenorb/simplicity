#!/usr/bin/env python3
"""Inventory primary published Simplicity applications; downloaded source is data."""
import datetime,hashlib,json,pathlib,urllib.request
out=pathlib.Path(__file__).resolve().parents[1]/'vendor-specs/application-sources';out.mkdir(exist_ok=True)
rows=[]
for repo in ['BlockstreamResearch/SimplicityHL','BlockstreamResearch/simplicity-contracts']:
 def get(url):return urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'jet-discovery-research'}),timeout=30).read()
 meta=json.loads(get('https://api.github.com/repos/'+repo));branch=meta['default_branch'];rev=json.loads(get('https://api.github.com/repos/'+repo+'/commits/'+branch))['sha']
 tree=json.loads(get('https://api.github.com/repos/'+repo+'/git/trees/'+rev+'?recursive=1'));assert not tree.get('truncated')
 (out/(repo.split('/')[-1]+'-tree.json')).write_text(json.dumps(tree,indent=2)+'\n')
 license_id=(meta.get('license') or {}).get('spdx_id','unknown')
 for item in tree['tree']:
  p=item['path']
  if item['type']!='blob' or not p.endswith(('.simf','.wit','.md')):continue
  if p.endswith('.md') and p not in ['README.md','LICENSE.md']:continue
  if p.endswith(('.simf','.wit')) and not any(x in p for x in ['examples/','simf/','source_simf/']):continue
  url=f'https://raw.githubusercontent.com/{repo}/{rev}/{p}';row={'repository':repo,'path':p,'revision':rev,'source_url':url,'license':license_id,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'data only; never compiled or executed'}
  try:
   raw=get(url);f=repo.split('/')[-1]+'_'+p.replace('/','_');(out/f).write_bytes(raw);row['local_file']=f;row['sha256']=hashlib.sha256(raw).hexdigest();row['status']='saved'
  except Exception as e:row['status']='gap';row['error']=str(e)
  rows.append(row)
(out/'provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['repository','path','status']} for r in rows],indent=2))
