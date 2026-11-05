#!/usr/bin/env python3
"""Render the complete new crypto-family scope/source and validation inventory.

Only actual runner exit statuses and observed vector lines count as evidence.
Reference checks, construction failures, and pending complete executions remain
separate from qualified corpus success. No cost is inferred from wall time.
"""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'reports/data'
def read(path,default):
 return json.loads(path.read_text())if path.exists()else default
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
FAMILIES=[
 ('crypto-blake3-tree-hash','component','Unkeyed BLAKE3,0–2048bytes→32bytes; all7rounds, blocks/chunks, real two-chunk parent/root','crypto-stream','blake3',22,'All19supported official unkeyed KATs;3length/canonical-padding/output negatives. All35upstream cases/all3modes inventoried.','BitVM chunk/wrap_hasher.rs directly invokes BLAKE3 for64/128/192/448byte field/accumulator commitments. The source truncates to16bytes; our32byte output is the complete standard prefix, not a full BitVM verifier.'),
 ('crypto-shake256-xof','component','SHAKE256,0–511bytes→250bytes; rate136/domain1f, up to4absorbs+2squeezes','crypto-stream','shake',17,'All6complete supported official NIST2000bit outputs;8derived rate/input boundaries;3length/canonical-padding/output negatives. All1619SHAKE256 source cases inventoried.','FIPS204 ML-DSA invokes SHAKE256; this is a PQ-authorization dependency, not evidence of deployed Bitcoin ML-DSA or a full signature verifier. No extra Keccak-permutation group.'),
 ('crypto-ml-dsa-ntt256','component','FIPS204 degree256 NTT+inverse; q8380417,zeta1753,all8stages and inverse scale8347681','crypto-stream','ntt',15,'6full polynomials in each direction checked against independent directDFT/inverse;3range/output/direction negatives. No official isolated NTT outputKAT found.','ML-DSA uses the complete transform for lattice signature arithmetic. This is a credible future Bitcoin PQ-verifier dependency; no claim of a current Bitcoin deployment or full ML-DSA verifier.'),
 ('crypto-poseidon2-koalabear16','component','KoalaBear q2130706433,width16,cubic S-box,8full+20partial rounds; two exact constant profiles','crypto-family','poseidon2',14,'Complete published Plonky3default16field KAT;10derived profile/boundary cases;3canonical-input/profile/output negatives. Exact Ziren profile outputs are derived, not an upstream KAT.','GOAT bitvm-gc default verifiable-circuit feature selects_poseidon2; Cargo.lock pins ProjectZKM/poseidon2→Ziren, whose exact constants are checked. This is a full permutation component, not a full garbled bridge verifier.'),
 ('app-webauthn-counter-wallet','full_spend_condition','Enrolled ES256 WebAuthn withdrawal; actual sig_all_hash challenge, RP/origin/UP+UV, canonical DER, monotone32bit counter and same-leaf native continuation','webauthn','full',17,'3positive native state transitions;14signed policy/canonical encoding/dataflow/state/value/transaction negatives. Integer P256 reference control matches RFC6979.','W3C WebAuthn Level2 authentication relation is adapted into native Bitcoin wallet authorization; enrollment/attestation/TLS are external. Counter-capable authenticators only; fixed37byte authenticatorData and bounded published clientData-prefix verification.')]
MODULES={'blake3':'Blake3','shake':'Shake256','ntt':'MlDsaNtt','poseidon2':'Poseidon2','full':'WebAuthn'}
def evidence(label,group):
 manifest=read(DATA/(label+'-full-provenance.json'),{})
 job=next((x for x in manifest.get('jobs',[])if x['group']==group),None)
 log=DATA/(label+'-'+group+'-verification.txt')
 text=log.read_text()if log.exists()else ''
 passed=len(re.findall(r'^\(".*",True,"',text,re.M))
 residency=re.search(r'([\d,]+) bytes maximum residency',text)
 # A multi-family driver also imports unrelated modules. Compare the selected
 # program's actual local import closure, preserving the full binary freeze.
 records={r['path']:r for r in manifest.get('source_files',[])}
 closure=set();todo=['src/JetDiscovery/Corpus/'+MODULES[group]+'.hs']
 while todo:
  rel=todo.pop()
  if rel in closure:continue
  closure.add(rel);record=records.get(rel)
  if record:
   source=(ROOT/record['frozen_path']).read_text()
   for module in re.findall(r'^import\s+(?:qualified\s+)?(JetDiscovery\.[A-Za-z0-9_.]+)',source,re.M):
    dep='src/'+module.replace('.','/')+'.hs'
    if dep in records:todo.append(dep)
 changed=[];compatible=[]
 for row in manifest.get('source_files',[]):
  if row['path']not in closure:continue
  p=ROOT/row['path']
  if not p.exists()or sha(p)!=row['sha256']:
   frozen=(ROOT/row['frozen_path']).read_text()
   old='    -- Outpoint hashes are stored in internal (little endian) byte order on the wire.\n    return (RawIn (Outpoint (hashFromBytes (BS.reverse h)) i) ss sq)'
   new='    -- Preserve the raw32 bytes. This is the in-tree Serialize Outpoint and\n    -- Bitcoin primitive API convention; explorer display strings reverse them.\n    return (RawIn (Outpoint (hashFromBytes h) i) ss sq)'
   if row['path']=='src/JetDiscovery/Tx.hs'and frozen.replace(old,new)==p.read_text():
    compatible.append('unused parseRawTx-only correction; builder functions identical')
   else:changed.append(row['path'])
 status='PENDING'if job is None else('EXIT0'if job['actual_exit_status']==0 else 'FAILED exit'+str(job['actual_exit_status']))
 return manifest,job,log,status,passed,residency.group(1)if residency else 'pending',changed,compatible
def main():
 lines=['# Crypto component families and WebAuthn wallet','',
 'Each component family counts at most once, independently of parameters, modes, input lengths or boundary vectors. Four component families and one native wallet are scoped here. Only a complete current vector batch with actual exit0 qualifies as passed. Reference-only success and compression-only success do not qualify the complete program. Runtime/residency below are validation resource measurements, never Simplicity costs. Fresh cost/what-if/mining rows remain **PENDING** until the common corpus analysis runs.','',
 '| Program ID | Scope | Complete vector evidence | Exit / seconds / maximum live bytes | Current source matches frozen executable? |','|---|---|---|---|---|']
 for ident,scope,spec,label,group,total,vectors,demand in FAMILIES:
  manifest,job,log,status,passed,residency,changed,compatible=evidence(label,group)
  seconds=str(job['elapsed_seconds'])if job else 'pending'
  qualified=job is not None and job['actual_exit_status']==0 and passed==total and not changed
  matches=('yes'+('; '+', '.join(compatible)if compatible else ''))if manifest and not changed else ('CHANGED: '+', '.join(changed)if changed else 'no frozen executable yet')
  lines.append(f'| `{ident}` | {scope} | {passed}/{total} observed; '+('**PASS**'if qualified else '**PENDING / NOT QUALIFIED**')+f' | {status} / {seconds} / {residency} | {matches} |')
 lines+=['','## Exact relations, test coverage and deployment paths','',
 '| Program ID | Checked relation | Vector inventory / gaps | Bitcoin path and limits |','|---|---|---|---|']
 for ident,scope,spec,label,group,total,vectors,demand in FAMILIES:
  lines.append(f'| `{ident}` | {spec} | {vectors} | {demand} |')
 lines+=['','The byte-oriented NIST ZIP contains8files. SHAKE256ShortMsg/LongMsg/VariableOut supply1619cases; exactly6have a complete2000bit output within the511byte input bound. SHAKE128, Monte Carlo, other output sizes and longer inputs remain explicitly outside this profile. This is not CAVP validation. BLAKE3 keyed/derive-key modes and longer inputs are inventoried but not claimed. See the complete machine-readable inventories in `vendor-specs/crypto-families/`.','',
 'The Poseidon2 profiles are one family. The primary authors\' BN254 example was acquired during source discovery but is not substituted for the inventoried Bitcoin-project KoalaBear profile. Plonky3v0.5.1 gives the complete published KAT; GitHub tag-resolution API access returned403, so the tag and SHA256 byte pins are preserved without inventing a commit. GOAT/Ziren profile outputs are independently derived from the exact pinned constants; its guest test has no published output assertion. No current mainnet adoption is inferred from repository use.','',
 '## Reproduction and execution paths','',
 'The Haskell compiler is GHC9.8.4 from the local Nix package environment. Direct builds use `-O1 -threaded -rtsopts -isrc`, the local `dist-newstyle/packagedb/ghc-9.8.4`, exact `-package-id Simplicity-0.0.0-inplace-Simplicity-Core`, `-package Simplicity -package jet-discovery`. NTT has compilation-only simplifier flags recorded in its source. The runner records the binary hash, complete local source closure, runtime KAT bytes, actual executable exit status and log hashes. Its own source is copied into each new freeze.','',
 'The current-source check above follows the selected program\'s local imports, rather than unrelated modules also linked by the multi-family driver. The complete original driver/source closure remains frozen. Tx.hs changed only in the unused parseRawTx function after the first WebAuthn/Poseidon2 build: a raw outpoint-byte reversal was removed. These entries exclusively use unchanged dummyOutpoint/mkInput/mkOutput/mkTx/mkEnv/defaultTap builders. The exact two-source diff and parent\'s codec audit confirm that this parser-only correction does not affect their fixtures. No other source difference is silently accepted.','',
 'Run the corresponding local driver binary with `tools/run_crypto_validation.py --label FRESH-LABEL --binary BINARY --build-dir BUILD-DIR --driver tools/CryptoFamilyVectors.hs --heap 16 --group blake3 --group shake --group ntt`. Every label is immutable; existing evidence is never overwritten. WebAuthn uses `tools/WebAuthnProbe.hs`, `--heap32 --group full`. Poseidon2 uses `--group poseidon2`. These commands validate the complete programs and actual same-CMR mutations.','',
 'Poseidon2 and WebAuthn use the prepared bound-program API: one aggregate witness followed by a pure witness-free kernel. Drivers assert canonical composition CMR equality and prepared-path observability. The three streamed component frontends deliberately use ordinary execution because independent block/output witnesses enter only at their consuming stages. Shared headers/inputs enter once and flow through projections. No equality between repeated witness occurrences is assumed.','',
 '## Retained failures and separate reference evidence','',
 'The earlier whole-array BLAKE3/SHAKE/NTT build each hit the16GiB cap during initial graph construction, before a vector result: actual exits251 and full frozen sources/logs remain under `reports/data/crypto-family-full-*` and the respective verification files. Their partial/compression/reference results never confer complete-program credit. Earlier4GiB Poseidon2 construction failures are likewise retained; the later complete14vector pass uses its recorded optimized build.','',
 'Independent reference audit: `reports/data/crypto-family-reference.txt` and `crypto-family-reference-status.json` (actual exit0). All19supported BLAKE3 KATs,6complete SHAKE KATs, all6ML-DSA polynomials against independent FIPS butterflies, and the published Poseidon2 KAT are checked. WebAuthn reference and22native hash/DER boundary helper checks are separate in `webauthn-reference.txt`, `webauthn-hashes.txt`, and `webauthn-helper-status.json`. They do not replace the full17wallet vectors.','',
 '## Provenance and licensing','',
 'Every acquired spec/source is inert data under `vendor-specs/crypto-families/` or the earlier `crypto-growth/` packet. No downloaded code is executed. URLs, revisions, licenses/access gaps and SHA256 hashes appear in the adjacent manifests; test extraction scripts parse numeric data without evaluating source code. All source rows, including discovery-only BN254 materials and source-access gaps, remain inventoried.']
 (ROOT/'reports/CRYPTO-FAMILIES.md').write_text('\n'.join(lines)+'\n')
 meta=read(ROOT/'vendor-specs/crypto-families/manifest.json',{})
 rows=meta.get('sources',[])
 m=['# Crypto-family source packet','',f'{len(rows)}resources inventoried; external code executed: false. All acquired source files are data, not build inputs. Generated Haskell constants come from explicitly parsed numeric arrays, checked by independent reference equations and KATs.','',
 '| File | Source URL | Revision | License / access note | SHA256 |','|---|---|---|---|---|']
 for row in rows:
  m.append('| '+row['file']+' | '+row['url']+' | '+row['revision']+' | '+row['license_note']+(' ACCESS GAP: '+row['access_gap']if 'access_gap'in row else '')+' | '+row.get('sha256','unavailable')+' |')
 m+=['','Extraction commands: `python3 tools/extract_crypto_family_kats.py`; `python3 tools/extract_poseidon2_data.py`. Every BLAKE3 and SHAKE256 source case is recorded with a supported/excluded verdict, not silently sampled. The raw ZIP and all8filenames are retained; extracted official files are unchanged. Derived TSVs use LF line endings.','',
 'FIPS204 is reused from `../crypto-growth/fips204.pdf`, not duplicated. WebAuthn Level2 and the independent RFC6979 control are attributed in the growth packet and source. No blanket repository license is inferred where no license was present.']
 (ROOT/'vendor-specs/crypto-families/MANIFEST.md').write_text('\n'.join(m)+'\n')
if __name__=='__main__':main()
