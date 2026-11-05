# Current validation checkpoint

The source milestone contains108 registered rows,104 distinct counting groups
and68 complete bounded spend/verifier groups. It does **not** meet the150-group
target. Old49-row cost/recommendation tables are historical and explicitly
withdrawn pending a complete fresh run. Vector-only evidence below supplies no
missing cost, profile, serialization or ablation numbers.

| Scope | Completed evidence | Remaining work |
| --- | --- | --- |
| Contract/Bitcoin expansion | All42 groups /202 vectors pass actual Bitcoin evaluation and same-jetted-CMR checks; [audit](CONTRACT-WITNESS-AUDIT.md) | Fresh shared cost/profile run |
| EVICT, BIP322, SPV receipt | All3 groups /27 vectors pass with actual TapTweak/TapLeaf funding outputs; [batch evidence](data/bitcoin-growth-batch1-provenance.json), [scope](BITCOIN-GROWTH.md) | Fresh shared cost/profile run |
| LMS | Official RFC8554 certificate4 and transaction7 vectors pass | Fresh shared cost/profile run |
| XMSS | All7 transaction vectors pass | Fresh shared cost/profile run |
| SHRINCS | Stateful12 and stateless7 vectors pass | Fresh shared cost/profile run |
| FIPS205 SHA2-128s | Independent reference passes all28 supported official cases; Simplicity official KAT4 passes | Native transaction7 group and fresh shared cost/profile run |
| Eprint relations | Expansion25 vectors, including FROST identity-commitment regressions, pass; six canonical-encoding control/attack pairs pass | Fresh shared full run; [detailed evidence](WITNESS-BINDING-AUDIT.md) |
| Ed25519 | All6 bound transaction-independent RFC/corruption vectors pass; [status](data/ed25519-bound-vectors-status.json) | Fresh shared cost/profile run |
| P-256 | Complete addition, canonical encoding and r+n carry unit regressions pass; earlier full-builder controls pass | Full8-vector run after pure-verifier sharing; no complete-group pass claimed |
| TXHASH | All150 upstream successful selectors plus derived wrong-hash negative pass, at one jetted CMR | Fresh shared cost/profile run; malformed selector decoding remains host-only |
| Older settlement/guard repairs | DLC settlement11, Merkle-key4, Uniswap-v2 kernel10, P2MR7 and modular multiplication6 pass | Remaining full upstream CTV/annex groups and fresh shared metrics |
| Full custom STARK | Honest full-size proof accepts at1,497,462.342WU; five small-parameter dataflow cases pass; [diagnostics](STARK-DIAGNOSTICS.md) | Full-size8-vector set and complete measurement/report fields |
| Analysis | New candidate/reference matcher checks pass; isolated and restricted-set costs agree with independent source substitution; current five fast regression checks pass | Complete current36-test suite and complete larger-corpus run |
| Upstream | Unchanged C suite98/98 passes in an archive copy | Complete default100-case Haskell suite rerun with12GiB cap after4GiB heap exhaustion |

All listed pass claims have observed successful exit status or a separately
identified completed test in a preserved cohort log. Interrupted/heap-exhausted
diagnostics are retained as failures or incomplete work. They never count as
passing programs. The first multi-type mining fixture accidentally let its
unused widths erase; the corrected fixture forces both widths through equality
checks and passes. Earlier cost-regression cohorts preserve that fixture failure
while separately recording their successful counterfactual-cost checks.

The full current suite, native standard-signature group, P-256 group, upstream
Haskell suite and BIP groups were still running when this checkpoint was written.
Their completion records must supersede pending rows before the final report.
Unregistered growth drafts receive zero count credit. Source inventories and
their access gaps remain explicit in the separate coverage reports.
