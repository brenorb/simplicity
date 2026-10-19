# Negation canonical correspondence: scoped review

This is source-review evidence, not an informal substitute for the formal C
proofs and not a complete transitive fidelity certificate. No registration or
acceptance is claimed. Reviewed target: `e3b670103101108faa238df012676ff5d8b77cf9`.

## Literal top-level chain

`CoreJets.hs` dispatches `FeNegate` to `Secp256k1.fe_negate` with FE -> FE.
The implementation record, not the earlier `mapLib`, defines negation as
`fe_multiplyInt (-1)`. Its local helper scribes `i mod fieldOrder`, pairs this
constant with the original input, and invokes `fe_multiply`. The Coq factor
uses `fromZ` at Word256 on exactly that remainder; no integer `p - x` program
replaces the canonical term. The integer identity is a proved intermediate
semantic bridge only.

`fe_multiply` is `mul256 >>> fe_normalize512`, with `mul256 = Arith.multiply
word256`. `fe_normalize512` pairs the Word512 input with the doubled-word
divisor `(zero256, fieldOrder)`, takes modulo at Word512 and projects its low
Word256 half. Coq specializes multiply at depth 8 and modulo at depth 9,
preserving both composition and low-half projection. The formal numeric
bridge separately proves that the high remainder half is zero from its bound;
the literal port does not drop that obligation by defining a numeric modulo.

`check-negate-wiring.py.source` freezes this wiring and the exact full public
theorem statement. Its 19 mutation fixtures all reject. The existing
normalization correspondence gate is responsible for the field-order constant,
FE = Word256, and comparison of the shared secp/core public frame contract.
That gate must also pass at eventual integration.

## Recursive multiplication inspected

Compared `Programs/Arith.hs:148-157` with `Simplicity/Word.v:313-330`.
The bit base pairs `take (cond iden false)` with the second product component,
then invokes bit full addition. Haskell `ih` here is Coq `drop iden`.
Both doubled-word builders have the same three composition stages and four
recursive multiplications; each `ooh`, `ioh`, `oih`, `iih` projection corresponds
to its explicit `O O H`, `I O H`, `O I H`, `I I H` Coq projection. Recursive
arguments and high/low result ordering agree. The public multiplication
wrapper pairs the operands with a doubled zero word before this recursion.

This comparison covers the multiplier's literal structure, not every
transitive bit/full-adder/notation/encoding dependency. The exact recursive
declarations are now frozen in `recursive-ports-review.json`, with typed-port
and implementation negative fixtures.

## Division core inspected

Compared `Programs/Arith.hs:246-280,315-320` with the definitions in
`C/jet_division_core_spec.v`. The Coq builder factors Haskell `div3n2n` over
the smaller `div2n1n` recursion without substituting a numeric algorithm.
Approximation, overflow, loop0, loop1 and loop2 preserve their predicates,
decrement, doubled addition, operand projections and result ordering. The
bit `div2n1n` base and doubled-word condition/body agree. The failed guard
still returns a doubled high word. `div_mod` preserves the zero-divisor branch
`(divisor, dividend)` and the pre-shift/divide/post-shift nonzero branch.

## Division normalization and typed adapters inspected

At remaining word depth `S n` and vector depth `m`, Haskell's `v' = vectorComp
vector2 v` becomes Coq vector depth `S m`, with remaining word depth `n`.
Both describe the unchanged total word depth `m + S n = S m + n`; Coq's
`eq_rect` transports the program along this arithmetic identity. The cast
does not introduce a numeric approximation or a different-sized domain.
Both base cases are `iden`. Both recursive steps test whether the leftmost
word-sized block of the divisor is zero, conditionally shift, and recurse
with those new indices.

The pre-shift branch uses left full shifts on dividend and divisor, projects
the retained large words, and preserves their ordering. The dividend's
additional doubling is Coq `full_left_word_spec n (S m)`, while the divisor
uses depth `m`. The post-shift branch prepends zero to the remainder, uses a
right full shift and projects the large word; its divisor still shifts left.
`division_leftmost_block` and `full_left/right_word_spec` transport the actual
Word leftmost/full-shift programs, not integer functions. Their inspected
typed bodies are included in the frozen review.

The existing full-shift correspondence gate passes for all 36 specializations
and literal recursive full-shift definitions; this is reusable evidence for
the direction/recursive programs, not new coverage or an exhaustive review
of vector type/equality/notation definitions.

The new recursive gate passes on both accepted and reconciled-range sources:
25 complete typed Coq declarations and six Haskell implementation/type regions.
Its 43 negative fixtures reject inactive commented declarations/implementations
and targeted changes to recursion, zero-divisor result ordering, pre/post
shift dimensions, cast indices, projection and direction. These tests freeze
the documented source review; they do not replace formal proofs.

## Still required before canonical review is complete

### Latest foundation receipt

The conversion/type/scribe/notation source boundary below now has a gate:
`check-foundations.py.source` passes and its pure in-memory suite rejects 32
mutations. It compares the inspected Haskell low-first state traversal with
the Coq port whose all-integer/depth equivalence theorem is closed and
kernel-checked. Word256/512 specialization, vector doubling and vectorComp,
canonical Either-bit mapping, Coq pair conversion, structural scribe and
base projection/composition/pair notation bindings match the inspected sources.
The Haskell state algorithm consumes low bits first but returns `(hi,lo)`;
the Coq pair representation has that same order. Both integer divisions are
floor division. Generic scribe maps units/sums/products to the same respective
unit/injection/pair combinators. Type aliases and vector constructors select
eight/nine doublings for Word256/512, not 256/512 Coq recursion depths.

This is scoped source correspondence evidence plus formal Coq bridges, not
a theorem translating arbitrary Haskell. Existing Coq kernel/CompCert/library
assumptions and the explicitly remaining shared-domain/evaluator review remain
unchanged. Historical "pin the conversion" instructions below are discharged
by this receipt. Candidate assembly still must include all sources and gates,
review actual new public types/definitions/assumptions, and run separate full
acceptance without snapshot-update flags before registration/integration.

The recursive snapshot/gate now also covers the inspected bit constants,
conditional/not/and/or/xor/majority, full-adder recursion, subtraction/borrow
inversion, decrement, comparison, complement, some/is-zero, fill and leftmost
adapters: **48 typed Coq declarations and 16 Haskell regions**. All 86 negative
fixtures reject, including targeted carry/borrow/bit/order mutations. The
earlier 25/6/43 counts above are historical, not the current gate scope.

The full-adder base `maj &&& xor3` matches Haskell `maj &&& xor_xor`; the bit
program bodies match the inspected canonical conditional nesting. Carry
recursion processes the low halves first and threads the carry into the high
halves in the same projections. Full subtraction complements the borrow and
second operand before full addition and flips the resulting carry; comparison
projects that borrow. Decrement supplies a true borrow and zero subtrahend.
The predicate's false specialization recursively ORs both halves and negates
the result for is-zero. Fill and leftmost use the same pair/take recursion.

Literal negation parametricity now passes whole-chain kernel checking (90456,
exit 0), with 15 existing library axioms and no unsafe flags.

`jet_haskell_word_conversion.v.source` ports the low-first `State Integer`
traversal of `Ty.Word.toWord`, retaining the final quotient. It formally proves
the result is `fromZ` and the remainder state is division by the word modulus
for every depth and integer. Whole compilation passes and the final theorem
is closed. Kernel checking passes with exit 0 (1799), with no unsafe flags.
Pin the inspected Haskell conversion,
word/type specialization, scribe and core notation sources with corresponding
negative fixtures before considering that remaining source boundary closed.

An explicit nonliteral adapter was found during arithmetic review: Haskell
`add w` always prepends `false` and invokes `full_add w`, whereas Coq
`Word.adder` has an optimized `adderBit` base. The division core uses the latter.
`jet_canonical_add_adapter.v.source` defines the literal canonical addition
term, proves it parametric, and proves its CoreFunSem denotation equals
`Word.adder` for every depth/input. The equality is closed under the global
context; compilation and whole-chain kernel checking pass (5720, exit 0).
This resolves the individual addition adapter semantically, not syntactically.
This bridge is now lifted by `jet_literal_division_add.v.source`: literal-add
approximation/correction loops, builder, recursive div2n1n/div3n2n, div_mod and
modulo all formally denote the existing optimized executor ports. Whole
compilation passes; the modulo equality uses only existing functional
extensionality. `jet_secp_negate_literal_contract.v.source` then connects this
literal modulo to normalize512/multiply/negate and proves
`fe_negate_literal_local_spec`, the same full public C contract against that
literal-add specification. Whole compilation passes and its final assumptions
are the six inherited execution assumptions. Independent whole-chain checking
of this final consumer **passes with exit 0** (32921), log
`/tmp/jet-fe-negate-next.GYJw0C/literal-contract-kernel.log`.
The exact literal-port gate now compares all ten typed division ports against
the reviewed definitions with precisely the literal-add substitution, plus
the canonical-add body, three field ports and full final contract. Its 15
mutations reject optimized-adder reintroduction and wrong recursion, widths,
projections, factors or public premises/bindings. The separate parametricity
module compiles; `literal_fe_negate_parametric` is closed under the global
context. Whole-chain checking runs as 90456. Finish remaining transitive
dependency review and full acceptance before integration/registration. The earlier
optimized-port public kernel receipt does not substitute for this new check.

- Finish transitive zero-test/vector type/equality/notation dependencies; the
  normalization and shift adapters themselves have the scoped review above.
- Reuse only actually applicable existing source reviews for bit combinators,
  addition/subtraction/decrement/comparison/high/zero and generic projections;
  review uncovered dependencies and constant/type conversion.
- Independent public kernel checking passes (10047). Complete snapshot/assumption review,
  source/negative gates and separate full acceptance on frozen inputs.

The public candidate retains arbitrary Word256 inputs and derives internal
normalized limb bounds from the real reader. No extra normalize call is added
to the public AST: the original writer already contains its own normalization.
