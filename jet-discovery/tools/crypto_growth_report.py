#!/usr/bin/env python3
"""Render every audited scope, preserving source/access/deployment/count gates."""
from pathlib import Path
import collections, csv, hashlib, json

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'reports/data'
scope_path=DATA/'crypto-growth-scopes.json'
manifest_path=ROOT/'vendor-specs/crypto-growth/manifest.json'
audit=json.loads(scope_path.read_text())
scopes=audit['scopes']
assert len(scopes)==20 and len({r['id'] for r in scopes})==20
assert audit['registered_programs_added']==audit['achieved_new_groups']==0
assert all(r['new_group_cap'] in [0,1] for r in scopes)
fields=['id','source','url','evidence','full_relation','native_path','overlap','missing_path','verdict','new_group_cap','priority']
assert all(set(r)==set(fields) for r in scopes)
with (DATA/'crypto-growth-scopes.tsv').open('w',newline='') as f:
 w=csv.DictWriter(f,fields,delimiter='\t',quoting=csv.QUOTE_ALL,lineterminator='\n');w.writeheader();w.writerows(scopes)

manifest=json.loads(manifest_path.read_text())
ok=[r for r in manifest['sources'] if 'sha256' in r]
gaps=[r for r in manifest['sources'] if 'access_gap' in r]
for r in ok:
 b=(manifest_path.parent/r['file']).read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
 if r['file'].endswith('.pdf'):assert b.startswith(b'%PDF-')
counts=collections.Counter(r['verdict'] for r in scopes)
esc=lambda s:str(s).replace('|','\\|').replace('\n',' ')
lines=['# CryptoGrowth deployment and independence audit','',
 'This is the complete bounded audit of the **20 scopes below**, dated '+audit['audit_date']+'. The audit itself adds **zero registrations or corpus-count credit**; implementation evidence is recorded explicitly per row and in the linked validation report. This is a source/deployment plan, not a cost measurement or a full-text review of the eprint archive.', '',
 'WebAuthn has a complete native wallet implementation with **17/17 full vectors PASS and actual exit 0**, including canonical composition CMR and prepared execution checks. [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md) records its evidence. FairSwap has a complete bounded native sale with **24/24 full vectors PASS and actual exit 0**, including all lifecycle and complaint paths, the fixed circuit wiring, and the protected input index. [FAIRSWAP-NATIVE-SCOPE.md](FAIRSWAP-NATIVE-SCOPE.md) records the exact scope and evidence. Fresh shared cost analysis is separate. Cashu requires a distinct native redemption/backing design and an explicit privacy tradeoff. The ten distinct full-verifier families and the cross-curve swap are substantial unfinished work. Four other rows are upgrades to existing groups; two have no established new onchain predicate.', '',
 'The arithmetic upper cap is fourteen possible new groups **if every gated scope becomes a complete, independently validated program**. This is neither a forecast nor evidence that fourteen near-term new applications exist. In particular, implementing a shared kernel or adding a signature/payout label does not earn that credit.', '',
 '| Verdict | Audited scopes | Registration/count credit from this audit |', '| --- | ---: | ---: |']
for k,v in sorted(counts.items()):lines.append(f'| `{k}` | {v} | 0 |')
lines+=['','The table retains every requested comparison in the primary artifact. The [machine-readable TSV](data/crypto-growth-scopes.tsv) and [source JSON](data/crypto-growth-scopes.json) contain the same twenty rows, including complete gap and deployment explanations. A cap of one means at most one distinct family/application after implementation; parameter, batch-size, threshold or frontend variants cannot multiply it.','',
 '| Scope and primary source | Evidence actually inspected | Complete checked relation | Native Bitcoin deployment | Existing overlap | Exact missing path | Verdict / maximum new credit |',
 '| --- | --- | --- | --- | --- | --- | --- |']
for r in scopes:
 lines.append('| '+ ' | '.join([f"`{r['id']}`<br>[{esc(r['source'])}]({r['url']})",esc(r['evidence']),esc(r['full_relation']),esc(r['native_path']),esc(r['overlap']),esc(r['missing_path'])+'<br>'+esc(r['priority']),f"`{r['verdict']}`; cap{r['new_group_cap']}"])+' |')
lines+=['','## Source coverage and reproduction','',
 f'The separate [source packet](../vendor-specs/crypto-growth/MANIFEST.md) records all {len(manifest["sources"])} retrieval attempts: **{len(ok)} valid retrieved documents and {len(gaps)} access gaps**. Eight direct eprint PDFs returned403; the legacy FairSwap author-dissertation endpoint returned a200 bot challenge rather than a PDF. Its exact university bitstream later yielded the genuine complete PDF. Both attempts remain recorded; the bot response is stored as HTML and is not counted as a retrieved paper. A successful HTTP status alone is insufficient.', '',
 'Complete existing BIP340/RFC9591/VT-Schnorr sources are reused from their original vendor directories and manifests. Primary metadata is adequate to retain a research lead, not to claim a complete protocol implementation or exclusion. The published WabiSabi PDF is a separate2021-08-25 revision with its own explicit CC BY4.0 notice; it is not silently substituted for the inaccessible current eprint revision.', '',
 'All external material is data outside the Haskell build. No downloaded code is executed. The Cashu source is MIT; the Babylon description is retained with its actual Business Source License1.1 text. RFC/IETF, W3C and PDF notices are recorded separately, without inferring a blanket software license.', '',
 '`python3 tools/crypto_growth_report.py` verifies packet hashes and renders every row offline. `python3 tools/fetch_crypto_growth_sources.py` intentionally refreshes the fixed documentary URLs and records any access failures; it should not be used merely to reproduce this snapshot.', '',
 'This audit itself adds no Cabal registration, CMR, WU or candidate-savings claim. The current source coverage inventory remains separate. WebAuthn, FairSwap and the separately approved crypto component families have their own frozen evidence. Other scopes do not inherit their vector results. Every implementation needs a single-entry witness dataflow audit, strict encoding and range checks, independent positive and adverse vectors, and the fresh main cost run.']
(ROOT/'reports/CRYPTO-GROWTH-SCOPES.md').write_text('\n'.join(lines)+'\n')

inputs={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [scope_path,manifest_path,DATA/'corpus-metadata.tsv',ROOT/'vendor-specs/bips/bip-0340.mediawiki',ROOT/'vendor-specs/eprint/rfc9591.txt',ROOT/'vendor-specs/eprint/vts-project-paper.pdf']}
(DATA/'crypto-growth-audit-inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
packet=['# CryptoGrowth documentary source manifest','',
 'This packet is separate from the frozen corpus milestone. External material is data only, outside the Haskell build; no downloaded code is run. These are source-audit inputs, not additional registered programs.', '',
 'Retrieval UTC: `'+manifest['retrieved_utc']+'`. Every one of the'+str(len(manifest['sources']))+' attempted resources is retained below, including failures. A PDF must begin with its actual `%PDF-` signature; the returned FairSwap bot HTML is not a paper.', '',
 '| Requested file | Source URL | Revision | Actual retrieval | License/notice |', '| --- | --- | --- | --- | --- |']
for r in manifest['sources']:
 status=(f"{r['bytes']}bytes; SHA256 `{r['sha256']}`" if 'sha256' in r else r['access_gap'])
 if 'response_file' in r:status+=f" Response `{r['response_file']}`, SHA256 `{r['response_sha256']}`."
 packet.append('| '+' | '.join([esc(r['file']),f"[source]({r['url']})",esc(r['revision']),esc(status),esc(r['license_note'])])+' |')
packet+=['','The complete preexisting sources `../bips/bip-0340.mediawiki`, `../eprint/rfc9591.txt` and `../eprint/vts-project-paper.pdf` remain in their original directories with their original manifests. Their current byte hashes are also captured in `reports/data/crypto-growth-audit-inputs.json`.', '',
 'The twenty-scope table distinguishes complete retrieved standards, selected protocol-path inspection, metadata-only paper leads and exact access gaps. It does not claim that a downloaded document was reviewed line by line. Metadata CC BY labels for inaccessible eprint PDFs are not applied to a different author/publisher PDF without its own notice.', '',
 'Reproduce the derived report offline with `python3 tools/crypto_growth_report.py`. Intentional online snapshot refresh uses `tools/fetch_crypto_growth_sources.py`; this executes only the repository-owned downloader and curl, never downloaded code.']
(manifest_path.parent/'MANIFEST.md').write_text('\n'.join(packet)+'\n')
print(json.dumps({'audited_scopes':len(scopes),'achieved_new_groups':0,'conditional_new_upper_cap':sum(r['new_group_cap'] for r in scopes),'verdicts':dict(counts),'valid_documents':len(ok),'access_gaps':len(gaps)},indent=2))
