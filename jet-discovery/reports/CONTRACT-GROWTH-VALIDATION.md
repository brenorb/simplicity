# Contract growth validation

**All eight registered growth applications passed all84 current functional
vectors.** The parent integrated them into the128-row/124-group corpus. Each
vector ran through `Run.runVectors`, including the canonical jetted-CMR check;
all logical witness values enter once before a closed pure kernel.

The previous owned expansion batch also completed42 groups/202 vectors, with its
separate actual witness-alias regression in `CONTRACT-WITNESS-AUDIT.md`. Those
older results are distinct from the84 growth vectors below.

| module | current application | vectors | result/evidence |
| --- | --- | ---: | --- |
| ContractGrowth | native nontransferable share vault | 10 | PASS, `data/contract-growth-final-guarded-vectors.txt` |
| ContractGrowth | asynchronous vault requests/fulfillment/claims/operators | 12 | PASS, same log |
| ContractGrowth | funded ascending auction | 10 | PASS, same log |
| ContractGrowth | funded sealed-bid auction | 12 | PASS, same log |
| ContractGrowth | indexed roles/votes/cancellation/delayed proposal execution | 18 | PASS, same log |
| ContractMessageApps | native Permit2 witness transfer and replay bitmap | 7 | PASS, same log |
| ContractMessageApps | compressed asset owner/delegate/root transfer | 7 | PASS, `data/contract-growth-final-resume16g.txt` |
| ContractBridge |184-byte guardian transfer, replay window and native payout | 8 | PASS, `data/contract-bridge19-vectors16g.txt` |
| **total** | **8 applications** | **84** | **all PASS; completed runs exit0** |

The first six completed69 vectors under an8GiB heap cap. That process then
exhausted heap while preparing the compressed-asset kernel. A16GiB resume
completed its seven vectors before exhausting heap during bridge preparation.
The final bridge run, after the two documented construction changes below,
completed all eight vectors under16GiB and exited0. Historical failed attempts
remain complete and are not attributed to another source version.

These are complete **bounded native adaptations** with the entry assumptions and
`CONTRACT-GROWTH-SCOPES.md` bounds. They do not claim foreign global storage,
current oracle freshness, a foreign mint/PDA derivation, raw VAA header/config
rotation, or an unavailable upper-time expiry primitive. Permit2 uses one native
reserve lineage, an opaque fixed adapter domain and a finite64-bit transfer
window; signed deadline expiry, explicit invalidation and owner recovery are
unsupported. Transaction nLockTime supplies a chosen lower bound.

## Source freeze and evaluation reuse

`data/contract-growth-freeze.json` records the exact current source hashes,
constructor adoption and the two explicitly authorized bridge exceptions.
ContractGrowth and ContractMessageApps bodies did not change during the final
runs. The vault's tenth vector rejects a reindexed state input, and all eight
applications require current input index0.

Each entry uses the parent's partially applied `boundProgram kernel . encode`
API. Canonical `unProg` remains exactly one aggregate witness followed by the
pure kernel. The prepared runner compiles the closed kernel once per batch,
checks each vector's input type and typed kernel fingerprint, and compares its
exact witness-prefix/kernel jetted commitment with the canonical whole-program
CMR. Unsupported/changed kernels fall back to canonical evaluation. There is no
globally cached whole-application DAG and no changed jet or benchmark price.

## Pure helper sharing evidence

`tools/CheckGrowthSharing.hs` completed ten comparisons. Each raw reference and
shared existing-jet wrapper has identical final jetted CMR, normal milliWU,
primitive-only milliWU, no-SHA ablation milliWU and exact serialized program and
witness bits. The first nine are in `data/contract-growth-sharing.txt`; the tenth
sealed commitment check is in `data/contract-growth-blind-sharing.txt`.

| helper | measured normal milliWU, equal before/after |
| --- | ---: |
| state hash | 43696 |
| full128-bit numerator/64-bit quotient and remainder | 419874 |
| Permit2 token permissions | 5973186 |
| native recipient witness | 5939522 |
| Permit2 struct | 11941166 |
| EIP712 envelope | 5939448 |
| BubblegumV1 leaf | 11904425 |
| ordered Keccak node | 5942882 |
| full184-byte VAA body and second Keccak | 17734548 |
| exact65-byte sealed commitment | 5968269 |

The separately tested minimal769-bit ecrecover operand helper completed all five
checks under8GiB (`data/ecrecover-sharing8g.txt`, exit0). Its normal and no-SHA
costs were6144179 milliWU each; primitive-only cost was647695103893154 milliWU.
Raw/shared values, final jetted CMR and exact program/witness encodings matched.
These are **helper costs**, not whole-application costs or candidate estimates.
Alternative jet matching reopens the specifications; the restricted-set checks
exercise that behavior. Raw pre-substitution CMR equality is not asserted.

## Bridge representation change

The parent first authorized replacing only the projected ecrecover call with
`Lib.Ecrecover.recoverShared` after the complete equivalence proof above. The old
source and SHA change record are retained in
`data/contract-bridge-before-ecrecover-sharing.hs.txt` and
`data/contract-bridge-sharing-change.json`. That16GiB bridge attempt still
exhausted heap before evaluating vector1.

The parent then authorized exactly19 optional guardian slots, replacing32 slots
whose trailing13 were already required absent. The new shape is a Vector16 plus
three explicit optional slots. It retains all actual13-of-19 address/signature
checks, the complete184-byte body and every original test vector. The negative
for nonzero72-byte **body** padding remains representable and passed.

Computed from these exact types, VInput's static width falls from21704 to15022
bits, eliminating6682 unused static bits. The native witness has13 fewer absent
flag bits. This is a representation change: **old/new program CMR or serialized
program equality is not claimed**. The old whole construction could not finish
at16GiB. The current canonical program was independently checked for every
final vector. Old source, hashes and the size calculation are retained in
`data/contract-bridge-before-19-slot.hs.txt` and
`data/contract-bridge-19-slot-change.json`.

## Historical attempts and reproduction

The8GiB and16GiB preparation failures remain in the logs named above. Earlier
whole-kernel sharing failures are in `data/contract-growth-sharing-whole8g.txt`
and `data/contract-message-vectors-whole8g.txt`. Other interrupted/pre-guard
construction runs and their scheduling status are retained in
`data/contract-growth-scheduling-status.json`. They receive no current-source
PASS credit. The auxiliary full-program FastEval/witness structural diagnostic
is in `data/contract-growth-fast-functional.txt`; it does not replace canonical
per-vector evidence or static pricing.

Reproduction uses pinned GHC9.8.4, the local package DB, explicit home source
modules and `tools/CheckContractGrowthAll.hs`, isolated output directories,
`-O1 -threaded -rtsopts`, and sequential runtime `+RTS -N1 -M16G -RTS`.
Group-ID arguments select the original completed six, compressed asset, or final
bridge. The parent owns Cabal/corpus registration, signed commits and fresh
whole-corpus measurement. Source-level local work changes no consensus jet,
cost table, encoding or off-limits tree.

## Six native applications, completed in a later batch

Six further native applications were outside this batch: conditional positions
29, indexed loan 20, signed order book 20, fixed-config OCR 11, three-claim
StableSwap 23 and weighted pool 18. They later passed all 121/121 vectors with
`tools/CheckNativeProtocols.hs` at a 32 GiB cap and are counted in the final
cohort; see [NATIVE-PROTOCOLS-VALIDATION.md](NATIVE-PROTOCOLS-VALIDATION.md).
The earlier 3 GiB conditional-positions preparation OOM is retained in
`data/claim-protocols-vectors.txt`. It receives no pass credit.

Separate mathematical evidence, with zero standalone application count:

* `CheckStableMath.hs`:12/12 actual get_D/get_y vectors, exit0 under3GiB,
  `data/stable-math-vectors.txt`.
* `CheckLogExp.hs`:46/46 bounded exact Balancer ln/exp/pow/rounding/error-envelope
  vectors, exit0 under3GiB, `data/log-exp-vectors.txt`.
* `CheckWeightedMath.hs`:11 quote/invariant vectors passed, then3GiB preparation
  OOM before LP-join vectors, `data/weighted-math-vectors.txt`; no completed join
  claim from this helper. The later full weighted-pool application covers joins
  ([NATIVE-PROTOCOLS-VALIDATION.md](NATIVE-PROTOCOLS-VALIDATION.md)).
* `CheckBoundedSqrt.hs`:116/116 exact128/256-bit integer-root vectors, exit0 under
  3GiB. The first run caught an incorrect Integer-reference sqrt(2) base case;
  that reference was corrected, the failure log retained, and dense0..100 plus
  maximum-width cases passed without changing the Simplicity algorithms.
