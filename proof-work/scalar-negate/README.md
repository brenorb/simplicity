# Original scalar-negate helper checkpoint

Five modules / 22 results prove actual in-place execution of the unchanged
`f_secp256k1_scalar_negate`, including its uint128 local allocation/free,
the original proved shift-by-64 call, void return, external memory framing,
and retention of the caller's 32-byte scalar ownership.

The actual four machine limbs are identified exactly. Their carry chain and
zero-input mask yield modular negation for normalized scalar inputs. The
final concrete loads reconstruct exact four-limb storage and construct the
existing writer representation, without assuming output or successful free.

Fresh compilation and independent `coqchk` completed with exit zero.
All 22 types and 15 non-tree definitions were reviewed untruncated; exact
per-result dependencies are recorded and checked: 17 closed, three with
four inherited classical dependencies, two with those plus CompCert
external/inline-assembly semantics. The imported kernel context has 15
inherited axioms, and all three unsafe categories are empty. No libc model,
new axiom, admission or unchecked proof tactic is introduced.

This is **internal support**, not a public scalar-negate jet proof, coverage
registration or full acceptance. The literal specification's multiply/mod512
composition still needs connecting to reader normalization, the serializer,
and actual public source-copy/entry/return/free. The normalized-input bound
belongs to this helper; the eventual public theorem must cover every Word256.
The unchanged scope is LP64, RECKLESS/assertion-disabled, inherited local
frame domain. Main shared registries and other authors' changes are untouched.

Materialized sources, exact commands, output hashes and terminal statuses
are in `manifest.json`. Verification from the repository root:

```sh
python3 proof-work/scalar-negate/review.py --work /tmp/jet-scalar-negate.f4CRAT
python3 proof-work/scalar-negate/test-review.py /tmp/jet-scalar-negate.f4CRAT
```

Scratch compiler load paths: accepted `C` baseline in
`/tmp/jet-ge-negate-accept.5mtyZa/Coq`, original scalar dependencies in
`/tmp/jet-scalar-reverify.8hswEF` (`OriginalC`), serializer dependencies in
`/tmp/jet-scalar-writer.khT8eN` (`WriterC`), and this checkpoint in
`/tmp/jet-scalar-negate.f4CRAT` (`NegC`). Compile with the pinned Coq 8.17.1
path and `ulimit -S -s 65520`, using `build-jets.sh --coqc/--coqtop/--coqchk`
and explicit narrow `-R` paths as recorded in the manifest.
