# Full Fibonacci STARK experiment

**Corrected full-size honest verification measured.** The earlier checked-hint expression
was vulnerable to same-CMR witness splitting. Its 1,416,983.723 WU result is a
historical consistency-schema benchmark, not a sound full-verifier cost.
The corrected verifier authenticates shared context reopenings and binds
every per-stage proof input through dataflow. The corrected expression costs
**1,497,462.342 WU** under the existing Bitcoin jets and accepts its honest
full-size proof. Full corpus negative vectors and reporting metrics remain
pending. See [STARK-DIAGNOSTICS.md](STARK-DIAGNOSTICS.md) for exact evidence and
[WITNESS-DATAFLOW.md](WITNESS-DATAFLOW.md) for the repair.

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
