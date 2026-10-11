# Literal scalar-negate bridge to actual C helper storage

Three modules / 14 results connect the unchanged in-place scalar negation
helper to the literal canonical scalar-negate program, retaining exact
four-limb storage and constructing the serializer's owned representation.
The helper result assumes only its represented scalar and its value supplied
by the canonical reader; it assumes no execution, output or successful free.

The literal port preserves the pinned Haskell composition, including
`unit >>> scribe`, full 256-by-256 multiplication, literal modulo with its
canonical-add calls, and projection of the low 256-bit half. Normalization
proves the discarded high half is zero. Its numeric meaning is proved for
**every Word256 input**, not only already reduced scalars. A connecting lemma
shows that the actual reader's preliminary normalization preserves negation.
All three program ports have formal Core parametricity proofs.

Reuse: the independently checked original C helper in `../scalar-negate`,
the scalar group constant/reader port in `../scalar-reader-zero`, existing
full multiplication and division semantics, and the accepted field-negation
literal-add division template. `scalar_limb_rho_value` reconstructs any
in-range 256-bit value from the shared serializer's four-limb valuation.

Fresh compilation and independent `coqchk` completed with exit zero.
All 14 types and four definitions were reviewed untruncated. Dependencies:
nine closed results, four using only inherited functional extensionality
(through the checked literal-division equality), and one actual execution
contract with four inherited classical dependencies plus CompCert external
and inline-assembly semantics. No new axiom or libc premise is introduced.
Imported kernel context: 15 inherited axioms; all unsafe categories empty.

The scoped literal-source gate checks group constants, catalog dispatch,
program bodies, recursive multiplier/division reference, and literal-add
substitution. It supplements Coq proofs; it is not a formal Haskell compiler
or a claim about all transitive source dependencies. Eight in-memory wiring
mutations and eight evidence mutations are rejected without changing audit
inputs.

**Not yet a public jet theorem, registered coverage or full acceptance.**
Actual reader/negate/writer composition and the public entry/source-copy/
return/free boundary remain. The execution scope stays inherited local
frames, LP64, RECKLESS/assertion-disabled. Other authors' work and the main
shared registries are unchanged.

Sources, drivers, exact output hashes and terminal check statuses are in
`manifest.json`. Reproduce from the repository root:

```sh
python3 proof-work/scalar-negate-canonical/review.py --work /tmp/jet-scalar-negate.f4CRAT
python3 proof-work/scalar-negate-canonical/test-review.py /tmp/jet-scalar-negate.f4CRAT
python3 proof-work/scalar-negate-canonical/test-literal.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-negate.f4CRAT /tmp/jet-scalar-reverify.8hswEF /tmp/jet-ge-negate-accept.5mtyZa/Coq
```
