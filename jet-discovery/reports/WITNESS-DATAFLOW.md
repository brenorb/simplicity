# Witness dataflow: same-CMR counterexample and repair rule

Repeated Haskell calls to `witness x` do not establish one logical Simplicity
variable. Witness values are excluded from the commitment root. Consequently
an attacker can supply different values to separate witness occurrences while
preserving the committed CMR. Sharing a Haskell expression or observing that a
particular DAG happens to merge identical values is insufficient.

The minimal executable counterexample is
[`tools/WitnessAliasing.hs`](../tools/WitnessAliasing.hs). It checks one witness
against zero and another against one. A builder that supplies the same value
to both rejects; independently supplying zero and one accepts. Actual output
from the in-tree jet substitution and evaluator is saved in
[`data/witness-aliasing.txt`](data/witness-aliasing.txt):

```text
("same jetted CMR",True)
("consistent witness outcome",Nothing)
("split witness outcome",Just ())
```

This is a defect in the corpus builder's assumptions, not an upstream
Simplicity mismatch. Existing consensus implementations are left unchanged.

A correct program must introduce a logical witness value once and route it to
all checks and uses through projections, `iden`, and ordinary dataflow. A
memory optimization may instead carry a cryptographic commitment and reopen
values, provided **each individual reopening enters once and is authenticated
and used in the same typed dataflow block**. Checking one witness copy does
not authenticate a later independently witnessed copy.

In particular, the initial Fibonacci STARK builder reused roots, OOD values,
opening pairs and transcript hints through repeated witness expressions. Its
fixed Haskell `Proof` API prevented the tests from supplying inconsistent
copies, but an arbitrary same-CMR spender is not constrained by that API.
The previously recorded full-size cost and honest outcome therefore describe
that consistency-constrained builder; they must not be presented as the cost
of a sound arbitrary-witness STARK verifier. Repair and fresh measurements are
required.

Regression tests must expose independently mutable copied fields or context
certificates, verify the adversarial term retains the same CMR, and assert
rejection. Testing only mutations of a Haskell record whose every use is
automatically changed together cannot detect this class of defect.

## Corrected Fibonacci compiler representation

`Corpus.FibonacciStark` now introduces the global tuple in one witness node:
trace root, composition root, FRI roots, four OOD answers, four AIR quotient
answers, and final FRI value. Transcript derivation and AIR checks use only
projections of that input. They produce the actual query seed and a context
Merkle root, which are carried as ordinary values through all query checks.

The context has sixteen fixed-position leaves. A leaf hash is
`SHA256(0x00 || uint8(index) || payload)`; an internal node is
`SHA256(0x01 || left || right)`. Indices are program constants, not witnesses.

| index | exact payload, in order |
| --- | --- |
| 0 | trace root (32 bytes), composition root (32), z (16), rho (16), four OOD values (4 × 16) |
| l + 1, for 0 ≤ l < number of folds | FRI root l (32), beta l (16), final FRI value (16) |
| remaining positions | empty byte string |

Hashes use their raw 32-byte SHA-256 encodings. A QM31 value is four canonical
M31 limbs, each encoded as a four-byte big-endian integer, matching the
Fibonacci transcript. The global input checks canonical field representations;
challenges are derived by the program. A reopening has a fixed four-sibling
path for its fixed index. The entire reopened payload is introduced once,
authenticated against the carried root, and retained for immediate check/use
through projections. Independently witnessed copies across stages are safe
because every copy is independently authenticated to the same carried
commitment; no copy relies on a check of a different copy.

Trace and composition opening pairs each enter once and flow through both
leaf authentication and DEEP calculations. Each reciprocal triplet enters
once and flows through inverse checks and the DEEP batch. Each subsequent FRI
opening pair enters once and flows through its incoming-value check, leaf
authentication and fold; its reciprocal enters once and flows through its
canonical/inverse checks and fold.

The first FRI pair is computed from the two DEEP batches and directly
authenticated against the first FRI root. It is not independently witnessed.
The Haskell reference `Proof` still contains that redundant first pair;
`verifier` derives the compiler representation from it, while the compiled
program does not serialize or read its values. This is an optimized proof
representation, not a claim of byte-for-byte compatibility with every field
of the reference record or a Stone/Stwo proof format.

`Ref.StarkContext` is an independent Haskell builder for the context paths.
The compiled verifier does not trust its root: it derives the root from the
single global witness. `verifierWithContext` exposes certificates separately
so tests can splice a context value without changing the global tuple.
`tools/StarkDataflowTests.hs` checks that such splices preserve the jetted CMR
and are rejected by the actual in-tree evaluator, alongside a valid proof and
modified inverse/opening cases.

## Additional corpus guard and authorization repairs

The older `bip360-p2mr-output` builder encoded its purported witness leaf CMR
with `konst`. It now introduces that leaf through a single witness node; a
changed leaf at the same committed output is an explicit rejection vector.
The BIP441 bounded modular-multiplication wrapper now rejects modulus zero.
The Uniswap-v2 kernel now enforces its stated positive, less-than-2^112 input
and reserve domain, including zero and width-boundary negatives.

The older `app-dlc-cfd` checked payout amounts but left their recipient scripts
unconstrained. It now commits both recipient script hashes, checks the input's
collateral statement, and clamps the oracle price before division. Re-signed
oracle attestations for zero and maximum Word64 prices exercise the payout
bound; diverted recipients and wrong collateral reject. The Merkle-key leaf
also has an explicit member-path/nonmember-signature negative. These changes
are confined to new corpus programs and alter their CMRs and costs; old result
rows remain historical until regenerated. The bounded vector run and actual
exit statuses are recorded in `data/root-corpus-repair-vectors.txt` and its
status JSON. An unfinished group is not a passing result.
