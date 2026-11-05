# STARK construction diagnostics

## Complete pre-final entry run

The normal runner completed all8 full-size vectors, every static measurement,
isolated candidate scenario, profile, serialization and applicable ablation.
Actual exit0,3839.262seconds, one capability,64GiB heap cap;54,460,241,664bytes
maximum live heap and66,578MiB total RTS memory. The honest generated proof
accepts; changed OOD answer, final constant, noncanonical trace field,
authentication sibling, DEEP inverse and independent initial/FRI context
splices all reject. Profile self-cost and root CMR consistency checks pass.

| field | completed value |
| --- | ---: |
| native static bound WU |1,497,462.342 |
| combined candidate overlay WU ESTIMATE |252,144.216 |
| encoded program bits, first vector |1,044,295 |
| encoded witness bits, first vector |1,248,640 |
| jetted DAG nodes |49,165 |
| bound without SHA256 jets WU |5,197,091,146.775 |

The exact21-scenario matrix, primitive baseline, all8 named outcomes and
snapshot hash are in
[stark-full-pre-final-measurements.json](data/stark-full-pre-final-measurements.json).
The full plain snapshot is `data/stark-full-pre-final.snapshot.txt`;
`data/stark-full-corpus-pre-final.{txt,json}` preserves executable/source
hashes, log and observed exit. It uses the same corrected native CMR below.
The later KoalaBear overlay addition and further corpus growth make this a
**pre-final entry result**, not a fresh complete-corpus ranking. No estimated
security-bit level or compatibility with Stwo/Circle proof encoding is implied.

The **corrected dataflow verifier** completed its full-size CMR, cost and
honest evaluation measurement on 2026-11-05:

| item | current corrected measurement |
| --- | --- |
| trace rows / LDE domain / queries | 1024 / 65536 / 48 |
| jet-substituted static cost | **1,497,462,342 milliWU = 1,497,462.342 WU** |
| jetted CMR | `12ad331f259e8c6ab3b85405e0585527930d7fa573c25da8ac339221312b1a08` |
| reference / honest Simplicity outcome | `True` / `True` |
| elapsed diagnostic time | 640.160 seconds |
| maximum live heap | 43,005,549,144 bytes |
| total RTS memory | 66,551 MiB |

The run used one capability and a 64 GiB heap cap. A 48 GiB cap had exhausted
the heap before completing CMR construction. Exact output and source-hash
provenance are in
[`data/stark-dataflow-full-64g-rts.txt`](data/stark-dataflow-full-64g-rts.txt) and
[`data/stark-dataflow-full-64g-provenance.json`](data/stark-dataflow-full-64g-provenance.json).
The measured module is also preserved as a text snapshot. Independent
same-CMR context-splice regressions at small parameters passed, as detailed
below. Full corpus negative-vector/report checks are separate work. This
custom DEEP/FRI protocol has no claimed proved security-bit level.

The later complete resource diagnostic
`data/stark-full-analysis-diagnostic.{txt,json}` exited0 in2313.146seconds
with54,590,809,296bytes maximum live heap and66,579MiB RTS memory under64GiB.
It timed CMR, native/primitive/combined-overlay/isolated-candidate costs,
serialization and profiling. That former diagnostic printed timings rather
than the values, did not assert acceptance and omitted ablations. It therefore
establishes construction capacity, not an additional accepted proof or a
complete analysis result. The normal runner's8-vector/full-analysis attempt
is preserved separately as `data/stark-full-corpus-pre-final.{txt,json}` and
must have a successful completion before any complete-group claim is made.
Its pre-final fingerprint will not be silently promoted to a later changed
corpus. The `time` command now prints evaluated results, checks profile
consistency, forces all ablations and asserts the first vector; the complete
ChaCha20 diagnostic exercises that reporting path in
`data/chacha-time-diagnostic-observability.{txt,json}`.

**Historical unsound-builder measurements.** The 1,416,983.723 WU result
below belongs to the earlier builder whose Haskell `Proof` interface forced
copied witnesses to agree. Arbitrary same-CMR witnesses can violate that
assumption. It is **not a valid full STARK verifier benchmark**. See
[WITNESS-DATAFLOW.md](WITNESS-DATAFLOW.md) for the executable counterexample.
The original logs and source-hash provenance are retained as historical data.
The current corrected measurement and adversarial regressions supersede them.

The full prover and the Simplicity term-construction pipeline are separate
measurements. `tools/StarkReferenceMemory.hs` fully forces a realistic proof
using `length (show proof)` and then runs the reference verifier. It completed
in about eight CPU seconds, returned `True`, and reached 271,720,264 bytes
maximum live heap (652 MiB total RTS memory). Its approximately 19.9 GB of
**cumulative allocation** is not resident memory. Exact output is preserved in
[`data/stark-reference-rts.txt`](data/stark-reference-rts.txt).

The original Simplicity construction failed much earlier than a complete
measurement: even the small trace/domain/query configuration exhausted a
3 GiB heap while constructing the **jet-substituted CMR**, before baseline,
what-if or profiling. The bare `CommitmentRoot` and `TermWeight` interpretations
completed quickly. These observations locate the problem in typed DAG
construction/substitution rather than in the FFT prover. They do not establish
which internal allocation site dominates; no change to the in-tree library
was made.

The historical empty-context architecture passed the small one-query honest
evaluation. An initial full 48-query CMR run exhausted a 6 GiB heap before a
cost result was produced. This failure is preserved in
[`data/stark-unit-full-rts.txt`](data/stark-unit-full-rts.txt) (approximately
6.318 GB maximum live heap, 110.5 seconds elapsed).

The identical historical full-size builder completed with a 24 GiB
heap cap and one capability:

| item | historical unsound-builder result |
| --- | --- |
| trace rows / LDE domain / queries | 1024 / 65536 / 48 |
| reference verification | `True` |
| withdrawn jet-substituted static cost | 1,416,983,723 milliWU = 1,416,983.723 WU |
| jet-substituted CMR | `81dcbce14a07036a091410297537d6be3ca04f6311f8e72adf7b1340c12482a3` |
| honest Simplicity evaluation | `True` |
| elapsed time, complete diagnostic | 268.192 seconds |
| maximum live heap | 13,193,910,176 bytes |
| total RTS memory | 24,959 MiB |

Exact output is in
[`data/stark-unit-full-24g-rts.txt`](data/stark-unit-full-24g-rts.txt), with
source hashes, parameters and invocation in
[`data/stark-unit-full-24g-provenance.json`](data/stark-unit-full-24g-provenance.json).
The historical cost is the in-tree `TermWeight` bound after the existing
Bitcoin jet substitution, with no candidate overlay. This diagnostic only
establishes construction, cost and the honest outcome under the unsound
consistency-constrained witness interface. It does not establish a valid
arbitrary-witness verifier. The complete corrected corpus
runner additionally checks the negative vectors, profiling, serialization,
ablations and what-if overlays. Neither a reduced-query cost nor this historical
result substitutes for a corrected full-size measurement.

The historical builder shared explicitly typed kernels, transcript prefixes
and query-index expressions, then checked copies of witness challenges in a
preflight phase. That optimization failed to bind later witness copies. Its
empty carried context is not used by the corrected authenticated-context
compiler described in [WITNESS-DATAFLOW.md](WITNESS-DATAFLOW.md).

Sharing alone preserved both the raw and jetted CMR of the original small
one-query program. The checked-hint architecture intentionally changes this
new corpus program's CMR and cost; it does not change an existing consensus
jet or program outside `jet-discovery/`. Historical diagnostic captures in
`data/stark-*-rts.txt` identify the stages of this investigation, not additional
corpus programs or security-parameter measurements.

## Corrected dataflow validation

The corrected verifier was tested at one query, trace log 4 and domain log 8
with `tools/StarkDataflowTests.hs`. All cases retained the same jetted CMR
`c0870683e42ed448d930b0519a9db55c615b50e56fcf99b34b3abf803fc8c0ec`.

| case | accepted? | expected outcome |
| --- | --- | --- |
| honest generated proof | yes | accept |
| initial context z independently spliced | no | reject |
| FRI beta context independently spliced | no | reject |
| incorrect DEEP inverse | no | reject |
| altered noninitial FRI pair | no | reject |

Exact evaluator results and RTS output are in
[`data/stark-dataflow-small-tests-rts.txt`](data/stark-dataflow-small-tests-rts.txt).
The run used one capability and an 8 GiB heap cap, with about 1.49 GB maximum
live heap. These are correctness regressions at small parameters, not a
full-size cost result.

## Reproduction

First build the normal project. From `jet-discovery/`, inside its Nix shell,
compile either diagnostic against the cached project library:

```sh
mkdir -p /tmp/stark-reference-diagnostic
ghc -O1 -threaded -rtsopts -outputdir /tmp/stark-reference-diagnostic \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  tools/StarkReferenceMemory.hs -o /tmp/stark-reference-memory
/tmp/stark-reference-memory +RTS -N1 -T -s -M4G -RTS
```

```sh
mkdir -p /tmp/stark-verifier-diagnostic
ghc -O1 -threaded -rtsopts -outputdir /tmp/stark-verifier-diagnostic \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  tools/StarkSmallVerifierMemory.hs -o /tmp/stark-verifier-memory
/tmp/stark-verifier-memory +RTS -N1 -T -s -M3G -RTS 1 4 8 -- rawcmr cmr cost eval
/tmp/stark-verifier-memory +RTS -N1 -T -s -M64G -RTS 48 10 16 -- cmr cost eval
```

The three numbers are query count, trace log and domain log. Omitting them
uses `Ref.FibonacciStark.small`. Available phases are `rawcmr`, `rawcost`,
`cmr`, `cost`, `baseline`, `whatif`, `bits`, `profile`, `candidates`,
`ablations` and `eval`; omitting phase names runs all phases sequentially.
RTS options must precede the program's `--` delimiter. The package DB path
must match the compiler used by the current build. No Cabal build runs inside
either diagnostic, and generated compiler objects stay in `/tmp`.
