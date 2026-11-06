# Full Fibonacci STARK experiment

**The full-size verifier passed all eight proof vectors in the frozen
cohort and cost 1,497,462.342 WU under existing Bitcoin jets.** It accepts
the honest proof and rejects all seven adversarial proofs under one
commitment. See the [exact-entry run record](data/stark-final-run.json),
[replay log](data/isolated-final-157-lf/stark-fibonacci-full-attempt1.txt),
and [measured profile](data/stark-full-final.snapshot.gz). The result
matches the [prior standalone diagnostic](data/stark-full-pre-final-measurements.json).

| Full verifier scenario | Bound (WU) | Selected candidate occurrences |
| --- | ---: | ---: |
| Existing Bitcoin jets | **1,497,462.342** | — |
| Primitive-only | 291,266,694,218.347 | — |
| SHA-256 jets removed | 5,197,091,146.775 | — |
| `m31_mul` only, **ESTIMATE** | 681,795.814 | 81,056 |
| `qm31_mul` only, **ESTIMATE** | 281,743.926 | 5,066 |
| `sha256_pair` only, **ESTIMATE** | 1,467,862.632 | 7,167 |
| Combined overlay, **ESTIMATE** | **252,144.216** | `qm31_mul`: 5,066; `sha256_pair`: 7,167 |

The jetted expression has 49,165 DAG nodes and 1,044,295 program bits;
the honest vector uses 1,248,640 witness bits before stack framing.
The overlays reprice the same expression. Their savings overlap and
their assumed prices do not come from new C benchmarks.

The fresh exact-entry run used a 64 GiB RTS cap. The coordinator records
4,307.506 seconds and the RTS records 4,361.561 elapsed seconds and
54,409,424,664 bytes of maximum Haskell residency. These describe the
research runner, including profiling and vector evaluation.

The earlier 1,416,983.723 WU expression allowed same-CMR witness splitting
and supplies no current verifier cost. The corrected expression binds
every per-stage proof input and authenticates shared context reopenings.
See [STARK-DIAGNOSTICS.md](STARK-DIAGNOSTICS.md) and
[WITNESS-DATAFLOW.md](WITNESS-DATAFLOW.md) for the exact evidence and repair.

This experiment measures the whole verification path, including the parts
omitted by `stark-fri-verifier`. It is a custom, non-zero-knowledge research
protocol. It uses a multiplicative subgroup in the quadratic extension of
M31, rather than the circle polynomial spaces or the Stwo proof format.
Its cost therefore measures demand for field and hashing primitives; it is
not a measurement of StarkWare's Bitcoin verifier.

The independent Haskell prover is `JetDiscovery.Ref.FibonacciStark`; the
Simplicity verifier is `JetDiscovery.Corpus.FibonacciStark`. Both are local
implementations. No downloaded implementation is executed.

## Statement and dimensions

| item | value |
| --- | --- |
| base field | M31, p = 2^31 - 1 |
| evaluation field | CM31 = M31[i]/(i^2 + 1) |
| challenge/answer field | QM31 = CM31[u]/(u^2 - (2+i)) |
| trace | 1,024 rows, Fibonacci starting with 1, 1 |
| public output | final trace value, computed by the reference recurrence and fixed in the program |
| low-degree extension | 65,536 points, rate at most 1/64 |
| coset | 3 times the order-65,536 subgroup of CM31 |
| FRI | ten binary folds to one constant |
| query draws | 48, independently derived with SHA-256 counter blocks; collisions are retained |
| commitments | SHA-256 binary Merkle trees; leaf = SHA-256 of four canonical big-endian field words |
| witness hints | field reciprocals; each is checked by multiplication |

These are realistic field, rate, and query dimensions rather than the
previous three-query toy experiment. They are **not a certified number of
security bits**. The implementation has no independent cryptographic audit,
Fiat-Shamir reduction, or implementation-specific soundness proof. In
particular, the 124-bit extension field, degree-dependent OOD error,
query collisions, and batching error must all enter a security analysis.
Do not infer 128-bit security from a query-count calculation alone.

## AIR and composition

Let N = 1,024, g be the order-N subgroup generator, and T interpolate the
trace on 1,g,...,g^(N-1). The transition numerator is

`T(g^2 X) - T(g X) - T(X)`.

It vanishes on all trace points except g^-1 and g^-2. Divide it by

`Z_transition(X) = (X^N - 1) / ((X - g^-1)(X - g^-2))`.

The other three quotients bind T(1)=1, T(g)=1, and T(g^-1)=public_output.
After committing T, derive alpha and combine the four quotients with
coefficients 1,alpha,alpha^2,alpha^3 into C. Commit C before deriving z.
The verifier checks the u-coordinate of z is nonzero, which excludes the
entire CM31 trace/evaluation domain. It checks the AIR at z, using the
answers T(z), T(gz), T(g^2z), and C(z). Denominators are cleared in these
equalities; no unverified division is used.

## DEEP and FRI

After binding the four OOD answers into the transcript, derive rho and form

```
D(X) = (T(X)-T(z))/(X-z)
     + rho   (T(X)-T(gz))/(X-gz)
     + rho^2 (T(X)-T(g^2z))/(X-g^2z)
     + rho^3 (C(X)-C(z))/(X-z).
```

For every query, authenticate both antipodal T values, both C values, and
all FRI layer pairs. Check the DEEP relation against the first FRI layer
at both X and -X. Each FRI fold is

`(a+b)/2 + beta*(a-b)/(2X)`.

The next domain point is X^2, with its sign adjusted to the representative
selected by the query bits. The last fold must equal the final constant.
Every opened field element, OOD answer, AIR quotient, and reciprocal hint
is checked for canonical coefficients below p.

The transcript binds the protocol version, all parameters, public initial
and final values, trace root, composition root, OOD answers, each FRI root,
and final constant before it selects query positions. Witness data changes
neither the CMR nor the verifier's control structure.

The implementation binds all global proof values in one structured witness.
It derives the transcript and a domain-separated 16-leaf context Merkle root
from that input. Each query or fold reopens its required context under the
same carried root, then uses the authenticated values through projections.
Leaf zero contains the trace/composition roots, z, rho and four OOD answers;
the next ten leaves contain the FRI root, beta and final value required by
each fold. The first FRI pair is computed from the authenticated trace and
composition openings by the DEEP relation, rather than supplied twice.
Each opening, reciprocal tuple and later FRI pair enters once at its stage.
Independent context-splice attacks reject at the same CMR in small-parameter
regressions. The host carrier also validates fixed list lengths,
32-byte hash lengths, and representability as Word32 before narrowing; the
on-chain expression checks field canonicality.

The honest DEEP polynomial has degree at most 1022; ten FRI folds test the
slightly looser degree bound below 1024. This local construction has no
formal soundness proof establishing the effect of that slack.

## Measured stage costs

These regions are taken from the native DAG of the complete corrected
verifier. A scratch probe computes the jetted CMR of each exact source
region. Its CMRs are matched against the saved profile, including the
expected 48 queries and ten folds per query. A CMR shared by different
witness values is accepted only when each matched cost agrees and the
selected-path multiplicities sum to the source call count.

| Nonoverlapping region | Calls on the static bound | Native WU |
| --- | ---: | ---: |
| AIR and out-of-domain check | 1 | 6,989.339 |
| Compute query's domain point | 48 | 183,015.036 |
| Trace Merkle path | 48 | 14,167.164 |
| Composition Merkle path | 48 | 14,243.964 |
| DEEP quotient batches, both sides | 96 | 463,069.536 |
| FRI Merkle paths across ten layers | 480 | 101,611.476 |
| FRI arithmetic after opening, including inverse check | 480 | 653,430.132 |
| Other nodes, including transcript, context reopening and control | — | 60,935.695 |
| Full verifier | — | **1,497,462.342** |

The three proof Merkle path rows include the two leaf hashes, path
traversal, query-index access and root equality. Together they cost
**130,022.604 WU**. The FRI arithmetic row also includes the post-opening
witness read, next-point calculation and final equality. The remaining
region includes the incoming fold equality, value canonicality and the
separate authenticated context paths. The table gives inclusive bounds for
these particular expression boundaries, not prices for new jet proposals.

The field multiplication rows are **overlapping**, both with each other
and with the stage table. Each M31 multiply costs **10.337 WU**, with
**81,056** selected calls contributing **837,875.872 WU** inclusively. Each
QM31 multiply costs **240.889 WU**, with **5,066** selected calls contributing
**1,220,343.674 WU** inclusively. QM31 multiply includes sixteen M31
multiplications. Don't add those two totals or add either to the stage table.

The [frozen native profile breakdown](data/stark-stage-final.json) is
reproducible from its [compressed snapshot](data/stark-full-final.snapshot.gz),
[stage roots](data/stark-stage-roots.tsv) and [field roots](data/stark-field-roots.tsv):

```sh
python3 tools/stark_stage_profile.py summarize \
  reports/data/stark-stage-roots.tsv reports/data/stark-field-roots.tsv \
  reports/data/stark-full-final.snapshot.gz
```

To regenerate roots, run `python3 tools/stark_stage_profile.py probe` and
`python3 tools/stark_stage_profile.py probe --fields` into two scratch `.hs`
files. Compile each with `cabal exec -- ghc -O1 -rtsopts -threaded -package
jet-discovery -package Simplicity` in the same Nix shell as the main build;
use separate scratch output directories. Run each binary with
`+RTS -N1 -A8m -M2G -s -RTS`. The stage probe took about 303 seconds;
the [stage RTS](data/stark-stage-roots-rts.txt) and
[field RTS](data/stark-field-roots-rts.txt) logs are separate from the full
verifier execution. The tool only joins measured native profile costs; it
doesn't replace the cost analysis or execute a second verifier.

## Reproduction and evidence

From `jet-discovery/`:

```
nix-shell --run 'cabal test --test-show-details=direct --test-option=--num-threads=1 --test-option=+RTS --test-option=-N1 --test-option=-M12G --test-option=-RTS'
nix-shell --run 'cabal run -v0 exe:jet-discovery -- run stark-fibonacci-full +RTS -N1 -A16m -M64G -RTS'
```

The first command compares FFT results with direct polynomial evaluation
and checks honest and tampered small proofs in the Haskell verifier. The
corpus command executes the full-size Simplicity verifier on the honest
proof, an altered OOD answer, an altered final constant, a noncanonical
opening, an altered authentication sibling, an invalid reciprocal hint, and
independent z/beta context splices. The normal full-corpus run records its measured bound, witness
size, profile, ablations, and candidate what-if costs in the same generated
tables as all other programs. The full verifier's row supersedes the old
FRI-only extrapolation for this specific experiment; the two protocols
have different fields, rates, and commitment depths and are not a direct
before/after benchmark.

The protocol is motivated by [DEEP-FRI, Ben-Sasson, Goldberg, Kopparty and
Saraf (2019)](https://eprint.iacr.org/2019/336). Its theorem does not by
itself prove this local composition, parameterization, or implementation.

## Historical, unsound full-size expression

The standalone full-size diagnostic succeeded on the frozen verifier source:
**1,416,983.723 WU**, jetted CMR
`81dcbce14a07036a091410297537d6be3ca04f6311f8e72adf7b1340c12482a3`.
The reference and honest Simplicity verifiers both accepted. Peak live heap
was 13.194 GB; elapsed time 268 seconds. Exact commands, source hashes and RTS
output are in [STARK-DIAGNOSTICS.md](STARK-DIAGNOSTICS.md). This is retained
only as historical diagnostic evidence and supplies no current verifier
cost. The corrected measurement uses CMR
`12ad331f259e8c6ab3b85405e0585527930d7fa573c25da8ac339221312b1a08`.
Its 64 GiB capped diagnostic took 640.160 seconds and reached 43,005,549,144
bytes of live Haskell heap while constructing and interpreting the typed DAG.
That construction memory is not a measured consensus evaluator RAM bound.
