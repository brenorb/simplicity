#!/usr/bin/env python3
"""Fetch only documentary data for the separate CryptoGrowth scope audit.

No downloaded program is executed or imported. The checked-in manifest records
HTTP failures as gaps; it never treats a metadata page as a retrieved paper.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import datetime, hashlib, json, subprocess

ROOT = Path(__file__).resolve().parents[1]
DEST = ROOT / 'vendor-specs/crypto-growth'
CASHU = '1363de413294e2ef3a57b16950f9506af38fffc2'
BABYLON = '8b9673c3ba5cff55b30865e876bfa4bf96bcd4b4'
IETF = 'IETF Trust BCP78/document license notice retained in source; not a blanket software license.'
SOURCES = [
 ('webauthn-2.html','https://www.w3.org/TR/2021/REC-webauthn-2-20210408/','W3C Recommendation 2021-04-08','W3C document-use/copyright notice in source.'),
 ('rfc9381.txt','https://www.rfc-editor.org/rfc/rfc9381.txt','RFC9381 2023-08',IETF),
 ('rfc9380.txt','https://www.rfc-editor.org/rfc/rfc9380.txt','RFC9380 2023-08',IETF),
 ('rfc8017.txt','https://www.rfc-editor.org/rfc/rfc8017.txt','RFC8017 2016-11',IETF),
 ('bbs-signatures-13.txt','https://www.ietf.org/archive/id/draft-irtf-cfrg-bbs-signatures-13.txt','draft13 2026-10-13; work in progress',IETF),
 ('fips204.pdf','https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf','FIPS204 2024-08-13','Official NIST publication; no additional license inferred.'),
 ('falcon-v1.2.pdf','https://falcon-sign.info/falcon.pdf','Falcon specification v1.2 2020-10-01','No separate PDF redistribution/software license inferred; source notice retained.'),
 ('fairswap-author-thesis.pdf','https://tuprints.ulb.tu-darmstadt.de/14041/7/lisa_eckey_dissertation.pdf','Author dissertation; publication/version inspected from PDF','No additional license inferred; source notices retained.'),
 ('fairswap-author-bitstream.pdf','https://tuprints.ulb.tu-darmstadt.de/server/api/core/bitstreams/0d999e6b-864a-4470-9a6a-984db287b388/content','Lisa Eckey dissertation; submitted2020-02-27, defended2020-04-24; URNurn:nbn:de:tuda-tuprints-140412','CC BY4.0 explicitly stated on dissertation publication page.'),
 ('wabisabi-published.pdf','https://assets.pubpub.org/xa8ue8wo/29539ffd-1b17-47d6-8acb-05293cd9f9ac.pdf','Published 2021-08-25','PDF explicitly states CC BY4.0; distinct published version from eprint.'),
 ('babylon-finality-README.md',f'https://raw.githubusercontent.com/babylonlabs-io/babylon/{BABYLON}/x/finality/README.md',BABYLON,'Repository license fetched separately; file is data only.'),
 ('babylon-LICENSE',f'https://raw.githubusercontent.com/babylonlabs-io/babylon/{BABYLON}/LICENSE',BABYLON,'Business Source License1.1; exact additional use grant/change terms retained verbatim.'),
 ('cashu-LICENSE',f'https://raw.githubusercontent.com/cashubtc/nuts/{CASHU}/LICENSE',CASHU,'MIT License, copyright2023 Cashu; retained verbatim.'),
]
for nut in ['00','03','10','11','12']:
 SOURCES.append((f'cashu-{nut}.md',f'https://raw.githubusercontent.com/cashubtc/nuts/{CASHU}/{nut}.md',CASHU,'MIT License; copyright2023 Cashu; LICENSE retained separately.'))
for path in ['README.md','FairFileSale.sol','RepeatedFairFileSale.sol']:
 SOURCES.append(('fairswap-'+path+'.txt',f'https://raw.githubusercontent.com/lEthDev/FairSwap/07f5664de64e232a0e1a8c0a84eefc223b45ae8b/{path}','07f5664de64e232a0e1a8c0a84eefc223b45ae8b; prototype linked by dissertation','Repository has no license file; no blanket license inferred. Solidity prototype stored/read only as data, not executed.'))
for paper in ['2022/1735','2021/206','2018/740','2018/1188','2018/623','2017/1066','2020/1126','2016/260']:
 SOURCES.append((paper.replace('/','-')+'.pdf',f'https://eprint.iacr.org/{paper}.pdf','eprint latest at audit time; only byte hash pins retrieved content','eprint metadata licenses are not silently applied to a different downloaded version.'))

def fetch(source):
 name,url,revision,license_note = source
 path=DEST/name
 temp=path.with_name(path.name+'.partial')
 r=subprocess.run(['curl','--fail','--silent','--show-error','--location','--max-time','45',url,'--output',str(temp)],capture_output=True,text=True)
 row={'file':name,'url':url,'revision':revision,'license_note':license_note,'curl_exit_status':r.returncode}
 if r.returncode:
  temp.unlink(missing_ok=True)
  row['access_gap']=r.stderr.strip()
 else:
  data=temp.read_bytes()
  if name.endswith('.pdf') and not data.startswith(b'%PDF-'):
   response=path.with_name(path.name+'.response.html')
   temp.replace(response)
   path.unlink(missing_ok=True)
   row.update(access_gap='HTTP success returned non-PDF content; bot/challenge page, not the requested paper.',response_file=response.name,response_bytes=len(data),response_sha256=hashlib.sha256(data).hexdigest())
  else:
   temp.replace(path)
   row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 return row

def main():
 DEST.mkdir(parents=True,exist_ok=True)
 with ThreadPoolExecutor(max_workers=4) as pool: rows=list(pool.map(fetch,SOURCES))
 manifest={'purpose':'Documentary source audit only; no corpus registration or achieved-count credit.',
           'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'external_code_executed':False,'sources':rows}
 (DEST/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
 for row in rows: print(row['file'], row.get('access_gap','OK'))

if __name__=='__main__':main()
