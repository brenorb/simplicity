# Upstream observations (reported, not corrected)

GOAL.md rule 5: disagreements or surprises in the upstream code are recorded
here with evidence, and the code is left alone.  The C code was not compared
with the Haskell or Coq code in this work, so no C/Haskell/Coq disagreement
was looked for, and none is reported.  The items below are cost and design
observations that affect jet selection.

## 1. `CheckSig.sigHash` constants are not constant-word jets (about 150 WU)

**Evidence.**
- `Haskell/Core/Simplicity/Programs/CheckSig.hs`: `sigHash` writes
  `scribe iv &&& iden` and `scribe (toWord512 0x8000…0400)` at input type
  `(Word256, Word256)`.
- Constant-word jets (`ConstWordJet`, matched in `Simplicity.Bitcoin.Jets`'
  `matcher`) only match constants whose input type is `()`.
- So when `sigHash'` is used outside the `CheckSigVerify` jet, the two
  constants are costed as combinator trees.
- `jet-discovery run app-htlc` with the library's `sigHash'` measured
  451.198 WU.  The same program signing `sig_all_hash` directly measured
  214.628 WU, and 62.340 WU once every constant in the program was also
  written as `unit >>> scribe c`.  The profile showed `pair : W512 -> W512`
  at 153.5 WU.

**Impact.**
- Inside `CheckSigVerify` there is none: the jet replaces the whole
  expression.
- Programs that compose `sigHash'` with their own signature check pay about
  150 WU per use.
- More generally, the cost of a constant depends on where it appears: about
  0.3 WU for a 256-bit constant at input `()`, tens of WU elsewhere.

**Suggestion for the library authors (not applied):** write constants as
`unit >>> scribe c`.  Compilers such as SimplicityHL should do the same.

## 2. The Bitcoin `Jet TermWeight` instance is not exported

**Evidence.**
- `Simplicity.Bitcoin.StaticAnalysis.Cost` (the Backpack instantiation of
  `Haskell/Indef/Simplicity/StaticAnalysis/Cost.hs`) is not listed in
  `reexported-modules` of `Simplicity.cabal`.
- `Simplicity.Elements.StaticAnalysis.Cost` is listed.

**Impact.** Static costs of Bitcoin programs cannot be computed from outside
the library without restating the two-line instance, as
`jet-discovery/src/JetDiscovery/Cost.hs` does.

## 3. `DivMod128_64` requires a normalized divisor

**Evidence.**
- `Haskell/Core/Simplicity/CoreJets.hs` (`implementationArith DivMod128_64`)
  returns all-ones unless `2^63 <= y` and `x < y * 2^64`.
- Its specification `div2n1n word64` is consistent with this.

**Impact.**
- There is no general 128-by-64 division jet.
- `app-dlc-cfd` had to shift the dividend and divisor by the divisor's
  leading zeros first.
- A first version that divided directly failed three of its vectors.

This is documented behaviour, not a bug.  It is listed because the
operation's limits are easy to miss when writing contracts.

## 4. Simplicity's annex hash differs from BIP 341's `sha_annex`

**Evidence.**
- `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:150` defines
  `InputAnnexHash` as `bslHash` of the annex bytes.
- BIP 341's `sha_annex` hashes `compact_size(len) || annex`.

**Impact.** BIP 446 (TEMPLATEHASH) and BIP 341-style signature hashes cannot
reuse Simplicity's annex hash.  `bip446-templatehash-exact` re-hashes
witness-supplied annex bytes.  This is a design difference, recorded because
it is part of the `bip341_hashes` candidate.

## 5. No Bitcoin budget rule in this repository

**Evidence.**
- `C/bitcoin/exec.c` takes `minCost` and `budget` as parameters.
- `C/limitations.h:9` fixes only `BUDGET_MAX = 4000050`.

**Impact.** Feasibility under a real budget cannot be decided here.
`reports/METHOD.md` states the assumption used.  This is the open question
for the user (GOAL.md: "Stop and ask the user when … the Bitcoin budget rule
can't be determined from the code").
