# Elements internal key and nullable tappath

These are **unregistered** implementation-to-specification proofs for two
Elements jets. They do not change main coverage (386/533 at preparation) or
stand in for either running whole-registry acceptance.

Private tree: `/private/tmp/jet-elements-tap-getters.jq5mpvwy`, copied from the
completed `elements-output-proof` tree, never from a running audit's objects.
All inherited source/metadata files are byte-identical except the one explicitly
reviewed, unregistered nullable-tappath module. Main Coq/C/Haskell and the original
staged patch are untouched.

## Actual C endpoints

- `elements_internal_key_literal_local_spec` transports the original
  `f_simplicity_internal_key` execution contract to the raw Haskell key encoding.
  Haskell's `Schnorr.PubKey` contains a native four-Word64 `Word256`, not a field
  element or a curve point. The checked big-endian byte/limb representation is
  reused without hashing, reduction, or a curve-validity premise.
- `elements_tappath_nullable_literal_local_spec` retains the original nullable
  path relation with length at most 128.
- `elements_tappath_u8_literal_local_spec` covers the C byte-sized path length,
  at most 255, using the same actual C proof. No pointer to path elements is
  required for an empty path. The full output, cursor, frame-separation and
  permitted-memory-change contract is retained in both versions.

The literal path adapter follows Haskell's `fromWord8`, `fromInteger`, `drop`,
`listToMaybe`, hash-word conversion, and absent/present tags. Its indexing helper
is polymorphic in logical word depth, but only the byte instance is claimed as
this Haskell `drop` correspondence: its checked range excludes native Int
overflow. Do not extrapolate that host conversion to arbitrary Word64 inputs.

## Shared proof and compatibility

`elements_tappath_env_rep_bounded limit` factors the existing environment relation.
Its 128 instance is **definitionally the original nullable relation**, witnessed
by `elements_tappath_nullable_128_unchanged`, whose right side is the complete
original predicate. The old theorem name and statement are retained. A closed
monotonicity lemma relates bounds, including nullable-128 to nullable-255.

`elements_tappath_bounded_local_spec` proves the C contract for any explicit
`limit <= 255`. The existing execution proof changes only its local numeric
bound from 128 to 255; no new execution/output premise is introduced. The
unchanged legacy endpoint is then an instance at 128, not a silently weakened
predicate. The 255 instance describes C-representable environments, not a claim
that protocol callers construct paths longer than their own limits.

## Verification and continuation

The generalized module and all three literal endpoints compiled with the pinned
Coq 8.17.1 normal compiler (OCaml 4.14.4), not the interactive backend's different
OCaml ABI. The source guard passed 50 in-memory corruption tests; no invalid
proof fixture was compiled. Four shared word/key/list conversion lemmas are
closed. C endpoints retain their original inherited assumptions, not an
axiom-free claim.

The full private checker was launched as **4458**; its fresh eleven-module
closure, independent old nullable baseline, complete type/definition/assumption
reports, source tests and Elements AST regeneration have passed. It is currently
performing recursive `coqchk`. Poll that handle; do not restart it because its
silent kernel log is quiet. Its successful terminal result is still required.

```sh
# Only for a fresh/retry run after the existing handle is confirmed terminal:
ulimit -s 65520
python3 -B proof-work/elements-tap-getters/check.py /private/tmp/jet-elements-tap-getters.jq5mpvwy

# After the checker succeeds:
python3 -B proof-work/elements-tap-getters/review.py
```

`review.py` separately compares the exact old nullable theorem types and
assumptions against the fresh original baseline, checks source/object/log hashes,
complete inventories and commands, and replays the source guard. Add independent
evidence-corruption tests before normal admission. A normal candidate must
explicitly review the inherited nullable-source generalization, register all
needed modules/results/definitions, preserve the old 128 contract, review the
snapshot delta, pass full acceptance and then install source-only. Do not count
three theorem versions as three jets.

The source correspondence guard is not a formal compiler for Haskell or a proof
of its host serialization/list libraries. These theorems do not establish real
caller construction of represented environments. LP64/RECKLESS and the existing
six inherited assumptions remain explicit boundaries. No new assumptions,
admissions, unsafe casts or skipped kernel checks are used.
