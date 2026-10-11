# Continue from actual reduce512 execution to the canonical public jets

Last verified declaration:
`MulC.jet_secp_scalar_reduce512_run.eval_scalar_reduce512_owned_loads`.
Fresh build **84956**, independent kernel **95049**, complete evidence
drivers **70464**, and read-only review/mutation tests all passed. There are
no live processes and no current failing Coq goal. `REVIEW.json` pins the
exact evidence. The unfinished obligation is the **numeric output identity**,
not an allocation/free/helper-call proof to redo.

## Scope and dependency chain

Public scalar multiply/square must eventually compose:

1. Existing scalar reader/canonical input and owned caller infrastructure.
2. The actual original `scalar_mul_512` full-product theorem, already checked
   in `../scalar-mul512/PRODUCT-REVIEW.json` (signed **338bfe1a**).
3. The actual original `scalar_reduce_512` call/load theorem in this archive,
   plus the still-missing numeric modulo-order output bridge.
4. Actual public caller/writer/cleanup and the literal canonical Simplicity
   multiplication/square specification bridge. Do not replace that spec with
   an integer modulo function merely because the helper arithmetic is done.

Existing final `scalar_reduce` and overflow helpers are checked in the
immutable dependency tree; reuse them. Main scalar-add candidate is fully
accepted, receipt **eecd0139**, but is not yet main registration. Keep its
inputs immutable and follow `../scalar-add-integration/CONTINUATION.md`
for exact integration, preserving staged/unstaged SHA and registry work.

## Critical width mismatch

`scalar_mul_512` declares `c2` as uint32. **`scalar_reduce_512` declares
`c0,c1,c2` as uint64**, while only `m6` and `p4` are uint32. The product
archive's `mul_column` / `column_rep` models the uint32 top, so its symbolic
top-field lemma cannot be applied unchanged to reduction.

Either introduce a triple-uint64 column with exact macro operations, or
prove a bounded embedding from the existing column model. Reuse the checked
unsigned product and carry facts. Any embedding/no-wrap guard is an internal
obligation to derive for the actual stages, never a new public call premise.
Also account for the real narrowing assignments into `m6` / `p4`, deriving
their range rather than silently equating truncated and unbounded values.

## Recommended finite-stage decomposition

Authoritative C: `C/secp256k1/scalar_4x64_impl.h`, non-ASM lines 513–580.
Authoritative generated AST: `Coq/C/jets_secp.v`, lines 56915–58962.
Do not regenerate or modify either accepted source just to simplify a proof.

Factor exact symbolic/machine operations for `muladd`, `sumadd`, their fast
variants and extraction. All multiplications should reuse
`umul128_unsigned_outputs`; all carry comparisons reuse the checked wrapped
addition lemmas. Fast variants need range proofs, not assumed no overflow.
Keep symbolic expression, machine carrier and unbounded value layers separate.
Derive the final symbolic output expressions by source binding and small
representation lemmas, as in the product archive. Do not unfold the complete
four-limb `den` array into an open arithmetic goal.

Let R = 2^256 and D = R - the canonical group order. These are arithmetic
bridge names, **not** replacement public specifications. Establish the exact
C constant identity D = C0 + 2^64*C1 + 2^128 from existing checked reduction
constant lemmas / literal constants before using it.

- First fold: seven limbs represent low256(input) + high256(input)*D.
  Prove its exact value and carry safety; derive its high256 part is at most
  D and `m6 <= 1`. Preserve the actual emitted digits and casts.
- Second fold: five limbs represent low256(first) + high256(first)*D.
  Use the actual value of D to derive D^2 < 2R, hence second < 3R and
  `p4 <= 2`. A loose D < 2^129 bound alone is insufficient for that sharp
  p4 bound; do not get stuck trying to prove it from only a bit-length bound.
- Third fold: the four pre-final limbs and `c` represent
  low256(second) + p4*D. With p4 <= 2, derive c <= 1 and value < 2*order.
  Relate the actual `c + scalar_check_overflow(r)` to the final reduction
  flag. If c = 1, the wrapped low part is below the order, so overflow is
  zero; otherwise it is the existing comparison flag. Thus the actual flag
  is 0 or 1, as required by the checked reduction arithmetic bridge.
- Each fold preserves value modulo the canonical order because R = order+D.
  Compose this arithmetic with the **actual** final loads/execution, then
  with original public callers and literal Simplicity specifications.

The bounds/identities above are the next proof obligations, not completed
theorems in this archive. Build short stage interfaces from downstream
needs, including carrier ranges; inspect the first failing goal after every
failure. Bounded tactic probes (10 seconds) and process deadlines, exact
module load paths, no admissions even in scratch, no source changes during
audits. No additional public coverage until the full canonical root checks.
