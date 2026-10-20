# Elements internal key and nullable tappath

These are **unregistered** implementation-to-specification proofs for two
Elements jets. They do not change main coverage (386/533 at preparation) or
stand in for either running whole-registry acceptance.

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
original predicate. The old theorem name and statement are retained. A
monotonicity lemma relates bounds, including nullable-128 to nullable-255. These
three memory-representation compatibility results retain four inherited
assumptions, as printed in the receipt; unlike the four conversion lemmas, they
are not closed under the global context. No new assumption is introduced.

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
