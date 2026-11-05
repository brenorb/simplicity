# Current validation checkpoint

The source milestone contains110 registered rows,106 distinct counting groups
and70 complete bounded spend/verifier groups. It does **not** meet the150-group
target. Old49-row cost/recommendation tables are historical and explicitly
withdrawn pending a complete fresh run. Vector-only evidence below supplies no
missing cost, profile, serialization or ablation numbers.

| Scope | Completed evidence | Remaining work |
| --- | --- | --- |
| Contract/Bitcoin expansion | All42 groups /202 vectors pass actual Bitcoin evaluation and same-jetted-CMR checks; [audit](CONTRACT-WITNESS-AUDIT.md) | Fresh shared cost/profile run |
| EVICT, BIP322, SPV receipt | All3 groups /27 vectors pass with actual TapTweak/TapLeaf funding outputs; [batch evidence](data/bitcoin-growth-batch1-provenance.json), [scope](BITCOIN-GROWTH.md) | Fresh shared cost/profile run |
| Silent payments and BIP127 reserve client | All9 native output-condition and7 client proof vectors pass the shared runner with prepared execution and stable historical CMRs; [scope](BITCOIN-GROWTH2.md) | Fresh shared cost/profile run; keypath bypass/client-mode boundaries remain explicit |
| LMS | Official RFC8554 certificate4 and transaction7 vectors pass | Fresh shared cost/profile run |
| XMSS | All7 transaction vectors pass | Fresh shared cost/profile run |
| SHRINCS | Stateful12 and stateless7 vectors pass | Fresh shared cost/profile run |
| FIPS205 SHA2-128s | Independent reference passes all28 supported official cases; Simplicity official KAT4 and native transaction7 pass; [completion](data/slh-standard-verification-status.json) | Fresh shared cost/profile run |
| Eprint relations | Expansion25 vectors, including FROST identity-commitment regressions, pass; six canonical-encoding control/attack pairs pass | Fresh shared full run; [detailed evidence](WITNESS-BINDING-AUDIT.md) |
| Ed25519 | All6 bound transaction-independent RFC/corruption vectors pass; [status](data/ed25519-bound-vectors-status.json) | Fresh shared cost/profile run |
| P-256 | Complete addition, canonical encoding and r+n carry unit regressions pass; earlier full-builder controls pass | Full8-vector prepared-kernel run; prior repeated-compilation run stopped after2 controls; no complete-group pass claimed |
| TXHASH | All150 upstream successful selectors plus derived wrong-hash negative pass, at one jetted CMR | Fresh shared cost/profile run; malformed selector decoding remains host-only |
| Older settlement/guard repairs | DLC settlement11, Merkle-key4, Uniswap-v2 kernel10, P2MR7 and modular multiplication6 pass | All389 CTV,19 template/annex and32 upstream P2MR vectors also pass; fresh shared metrics remain |
| Full custom STARK | Honest full-size proof accepts at1,497,462.342WU; five small-parameter dataflow cases pass; [diagnostics](STARK-DIAGNOSTICS.md) | Full-size8-vector set and complete measurement/report fields |
| Analysis | Full39-test suite passes1026.51s; explicit prepared-path3-case checks pass, including changed source/type fallback and actual path selection | Complete larger-corpus run remains |
| Upstream | Unchanged C suite98/98 and Haskell suite3252/3252 pass; default100 QuickCheck cases, no filter; [completion](data/upstream-validation-status.json) | No further upstream source changes are planned |

All listed pass claims have observed successful exit status or a separately
identified completed test in a preserved cohort log. Interrupted/heap-exhausted
diagnostics are retained as failures or incomplete work. They never count as
passing programs. The first multi-type mining fixture accidentally let its
unused widths erase; the corrected fixture forces both widths through equality
checks and passes. Earlier cost-regression cohorts preserve that fixture failure
while separately recording their successful counterfactual-cost checks.

The P-256 group and full-STARK analysis diagnostic were still running when this
checkpoint was written. The39-test cohort and all BIP cohorts now pass; their
completed records are in data/harness-prepared-current39.json and
data/root-corpus-repair-vectors-status.json. The latter driver captured only its
initial executable hash; later prefix binaries may have been rebuilt, which is
explicitly recorded rather than silently attributed to that initial hash. The earlier36-test
completion was observed in the tool result (1489.31s); its Cabal-generated log
was removed during reconfiguration before preservation. The current cohort
uses `tools/run_recorded.py`, which freezes the executable and captures output
and launch source hashes directly. The preserved39-test completion supersedes the older36-test observation;
the final frozen corpus still requires its complete shared run.
Unregistered growth drafts receive zero count credit. Source inventories and
their access gaps remain explicit in the separate coverage reports.
