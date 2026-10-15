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

The full private checker **4458 terminated with exit 0**, including its fresh
eleven-module closure, independent old nullable baseline, complete type/definition/
assumption reports, source tests, Elements AST regeneration and recursive
`coqchk`. `PREPARATION.json` and the complete logs bind this result to input
`2a6bde9f69ca75da50c5a150959ebf4abb2914ae2a353d1e1060c7ef087bd08a`.
The proof closure contains 65 results and 35 definitions. The literal module adds
nine results (including three whole endpoints) and four definitions. Exactly
1,585 inherited source/metadata files retain their bytes; the nullable module's
generalization is the sole reviewed inherited-source change.

```sh
# Historical completed command; do not overwrite these recorded objects or
# receipts. For reproduction, copy the proof folder/tree and use new paths.
ulimit -s 65520
python3 -B proof-work/elements-tap-getters/check.py /private/tmp/jet-elements-tap-getters.jq5mpvwy

# Independent review of the successful recorded check:
python3 -B proof-work/elements-tap-getters/review.py
python3 -B proof-work/elements-tap-getters/test-review.py
```

`review.py` separately compares the exact old nullable theorem types and
assumptions against the fresh original baseline, checks source/object/log hashes,
complete inventories and commands, and replays the source guard. Its review
passed, as did 38 independent evidence-corruption fixtures, including a forged
legacy-type report whose log hashes were made internally consistent. The
durable `EVIDENCE-REVIEW.json` binds the independent review/negative commands,
successful exits, their logs, the preparation receipt, and the reviewer tools.
A normal candidate must
explicitly review the inherited nullable-source generalization, register all
needed modules/results/definitions, preserve the old 128 contract, review the
snapshot delta, pass full acceptance and then install source-only. Do not count
three theorem versions as three jets.

The source correspondence guard is not a formal compiler for Haskell or a proof
of its host serialization/list libraries. These theorems do not establish real
caller construction of represented environments. LP64/RECKLESS and the existing
six inherited assumptions remain explicit boundaries. No new assumptions,
admissions, unsafe casts or skipped kernel checks are used.

## Next integration step

Both older normal audits were confirmed live after this checker completed:
actual-main 386 as **92335**, and isolated 399 as **61966**. Their source inputs
remain frozen. Do not copy compiler objects from either live audit or start a
replacement on silence. The 399 candidate first needs its guarded source-only
installer/postcheck, after both terminal acceptances pass.

Then prepare a successor including these two jets (not three), carrying the
explicitly reviewed nullable source generalization. The old nullable type and
predicate must remain at 128, the added endpoint at 255, and every original
public assumption set must be preserved. Run the normal whole build, source/
negative guards, full actual type/definition/assumption-delta review, and full
isolated acceptance before installation. A proof-folder receipt is not that
normal acceptance. Keep main's prior staged patch unchanged.
