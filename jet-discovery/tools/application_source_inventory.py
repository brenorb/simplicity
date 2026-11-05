#!/usr/bin/env python3
"""Triage every file in the pinned Simplicity example/source inventory."""
import collections,json,pathlib,re
root=pathlib.Path(__file__).resolve().parents[1];folder=root/'vendor-specs/application-sources'
rows=json.loads((folder/'provenance.json').read_text())
def verdict(r):
 p=r['path'];name=pathlib.PurePosixPath(p).name
 if r['status']!='saved':return 'access gap',r.get('error','unknown')
 if name.endswith('.wit'):return 'upstream witness retained','Foreign transaction/genesis environment; retained as data, not silently treated as a Bitcoin vector. Bitcoin adaptations derive and label their own environment vectors.'
 if name=='README.md':return 'source context','Repository scope, build boundaries and license evidence; never executed.'
 if '/artifacts/' in p:return 'duplicate generated source','Same application as the simf source path; never counted again.'
 if name=='hodl_vault.simf':return 'Bitcoin adaptation','ProposalApps app-hodl-price-vault: signed height/price bytes plus owner spend signature; no upper-time freshness claim.'
 if name=='non_interactive_fee_bump.simf':return 'Bitcoin adaptation','ProposalApps app-noninteractive-fee-bump: custom signed fields and checked bounded Bitcoin fee sums replace Elements fee introspection.'
 if name=='sighash_all_anyonecanpay.simf':return 'scope adapted into full application','ProposalApps app-assurance-crowdfunding: output-bound ACP pledge plus threshold funding and authenticated donor refund; helper is not counted separately.'
 if name=='bytes32_tr_storage.simf':return 'Bitcoin adaptation','StatefulApps app-native-state-counter: preserve upper192 bits/increment low64; native NUMS internal-key state commitment replaces a TapData sibling.'
 if name=='simple_storage.simf':return 'foreign asset semantics excluded','Source encodes storage via asset amount and mint/burn; Bitcoin has no asset/issuance primitive. StateMachines owner-authenticated data store borrows only the authorization idea, not this asset protocol.'
 if name=='array_tr_storage.simf':return 'not counted / storage component','Fixed-array commitment/update kernel; not turned into extra application rows or parameter sweeps.'
 if name in ['option_offer.simf','options.simf']:return 'not a native Bitcoin contract port','Requires Elements assets, explicit asset/amount checks, issuance/reissuance and asset-aware outputs. Cash-settled native BTC oracle applications are documented as different adaptations.'
 if name in ['presigned_vault.simf','escrow_with_delay.simf','htlc.simf','last_will.simf','transfer_with_timeout.simf']:return 'covered family / no duplicate count','Related vault, escrow, HTLC, inheritance and two-party timeout policies already appear in Apps/BitcoinExpansion. Renaming a policy or changing its delay does not add a program.'
 if name in ['p2pk.simf','p2pkh.simf','p2ms.simf','ctv.simf']:return 'covered baseline / no duplicate count','Basic authorization or CTV already in the corpus; upstream representation is retained for source comparison.'
 if name.startswith('sighash_'):return 'signature-hash component / no extra application','Sighash scope is a kernel or proposal component, not a standalone full application. Bitcoin/Elements fields differ and must not be silently substituted.'
 return 'compiler/example component / not counted','Language constructs, module/dependency packaging, array folds or hash loops; no distinct complete Bitcoin spending application identified.'
lines=['# Published Simplicity application source scan','','Both complete Git trees are pinned in `vendor-specs/application-sources/*-tree.json`; each was asserted untruncated by the retrieval script. The selection is every `.simf`/`.wit` under examples, simf or source_simf paths, plus repository README files. All selected files are listed below, including generated duplicates and non-applications. No downloaded code was compiled or executed.','','Coverage: '+str(len(rows))+' selected files; '+str(sum(r['status']=='saved' for r in rows))+' retrieved; '+str(sum(r['status']!='saved' for r in rows))+' access gaps. Every file was inventoried and mechanically inspected for functions/jets; semantic review concentrated on application candidates. Compiler demonstrations are not claimed to have received a full security review. A source record is not a counted corpus program.','','Bitcoin adaptations use native transaction primitives and explicitly disclose differing state/asset/time models. No existing Elements implementation or tests were changed. The published presigned-vault source even names an Elements `broken_do_not_use_check_lock_distance` function; Bitcoin adaptations use the in-tree Bitcoin timelock program rather than executing or copying that call.','','Reproduce inventory from saved data: `python3 tools/application_source_inventory.py`. Refresh source data: `python3 tools/vendor_application_sources.py` (network access, new pinned revisions).','','| repository / path | revision | inspected source facts | verdict | reason / application mapping |','| --- | --- | --- | --- | --- |']
counts=collections.Counter()
for r in rows:
 v,reason=verdict(r);counts[v]+=1
 text=(folder/r['local_file']).read_text(errors='replace') if r.get('local_file') else ''
 facts=str(len(text.splitlines()))+' lines; '+str(len(set(re.findall(r'jet::([A-Za-z0-9_]+)',text))))+' distinct jet names'
 lines.append(f'| [{r["repository"]}: `{r["path"]}`]({r["source_url"]}) | `{r["revision"]}` | {facts} | {v} | {reason} |')
lines+=['','## Counting and witness-flow validation','','Only complete `Entry` programs passing the actual Bitcoin evaluator and commitment-invariance checks can count. Alias-sensitive code must materialize each logical witness once and then use projections; repeating the Haskell expression `witness x` does not constrain those copies to be equal at the same CMR. This requirement applies equally to programs adapted from a high-level source. See the root witness audit and `Regression/WitnessState.hs` for an executed state-counter attack and its repair.','']
(root/'reports/application-source-scan.md').write_text('\n'.join(lines))
print(dict(counts))
