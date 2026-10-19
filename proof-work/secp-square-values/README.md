# Original optimized square: numeric and literal helper boundary

This packet advances the actual C square proof beyond execution alone. It is
**not yet a public square-jet equivalence or accepted coverage**.

The endpoint is
`SquareValue.Spec.eval_original_square_literal_from_reader`.
For every unrestricted Word256 input, given its established normalized-reader
representation in owned storage, it proves an actual call to the original
`f_secp256k1_fe_sqr`, all five resulting memory loads, the output's equality
under the existing writer encoding to the literal Simplicity square term,
the writer's required limb bounds, and framing outside the local region.
It does not assume the helper executes or assume its numeric result.
It does not execute the public jet's reader, writer, or allocation/free lifecycle.

## Proof structure

- `Algebra` gives injectivity and modular accumulation rules for the already
  verified two-word machine operations.
- `Columns` proves all seven symmetric-column replacements used by the real
  optimized squarer, including the bounds making each 64-bit doubling exact.
- `Schedule` names the actual symbolic squaring schedule.
- `Equality`, `Link`, and `Lists` link all five schedule outputs to the actual
  original C execution in `../secp-square-execution`. Four checks use conversion;
  the larger fifth uses a proved Boolean equality recognizer. Its unsupported
  syntax returns false; the concrete source comparison must compute to true.
  No unchecked conversion or equality assumption is used.
- `Denote` transports the optimized machine schedule to the checked multiplier
  with identical operands. The square's signed right shift is kept literally:
  it agrees with the multiplier's unsigned shift because the masked operand
  is nonnegative. Neither implementation nor specification was changed.
- `Numeric`, `Execution`, and `Spec` reuse the multiplier's reduction and bounds,
  obtain the actual output loads, and connect the result to the literal term.

The specification bridge is intermediate infrastructure, not a replacement for
the requested public C-to-specification theorem.

## Checks and exact-input scope

The private extension is `/private/tmp/jet-square-values.JhhZ8P`, with namespace
`SquareValue`, on the checked ordinary basis
`/private/tmp/jet-beta-integration-qctc10_1` and the checked `SquareRun.Run`
extension. Ten modules are freshly compiled in dependency order. The full report
covers 64 results and 47 definitions, and binds 223 loaded local dependencies.
The observed result profiles are 59 closed, one with four inherited assumptions,
two with dependent functional extensionality alone, and two C-call endpoints
with the same six inherited assumptions as the execution foundation.

Run `python3 -B proof-work/secp-square-values/verify.py` with `compile`, `kernel`,
or `check` from the repository root. Compilation and kernel runs are one-shot;
poll their original process handles. `RUN.json` records compilation and full
type/definition/assumption reports. Only a terminal successful `CHECKED.json`
with its matching recursive kernel log establishes the kernel stage. A launch
record alone does not. The receipts apply only to their recorded exact source,
object, dependency, driver, and main-input identities; this is not a portable
clean-checkout build or normal registry acceptance claim.

## Next public-jet obligations

1. Build the one-owned-region input representation from the real reader's
   `fe_at` result, reusing `owned_field_region`.
2. Transport the actual symbolic output representation to the existing wide
   writer input contract, retaining Freeable ownership and the precise frame.
3. Compose `eval_local_read_fe_canonical`, this actual square call, and
   `eval_local_wide_write_fe`. The beta chain is a useful template, but the
   square has no beta-global readiness premise.
4. Prove actual public entry, by-value source copy, return and local frees,
   then expose the existing general local-frame contract against
   `literal_fe_square`. Do not replace those steps with new execution premises.
5. Attempt normal isolated registration without bypassing unrelated frozen
   identity/domain failures. Accepted coverage remains zero for this packet.
