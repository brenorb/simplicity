# Original optimized C square: execution foundation

This packet proves execution of the original `secp256k1_fe_sqr` wrapper and its
optimized squaring inner routine. It does **not** yet prove equivalence of the
public `simplicity_fe_square` jet to its Simplicity specification.

`Run.v.source` is the archived source of `SquareRun.Run` in
`/private/tmp/jet-square-execution.eFdtoj`. Its ordinary dependency basis is the
checked tree `/private/tmp/jet-beta-integration-qctc10_1` from
`../secp-beta-integration`.

`eval_original_square_owned_inplace` establishes an actual Clight call with
identical input/output pointers, a five-limb owned output representation, and
memory framing outside that region. Its symbolic output comes from the real
optimized squaring code, not a substituted multiplication implementation.
The module also records the literal specification wiring and its numeric
meaning. Those specification lemmas alone are not C-to-specification proofs.

The compiler and assumption audit cover 12 results and 6 definitions. The
execution theorem has the same six inherited assumptions as its checked
interpreter basis; the closed execution/shape computations introduce none.
`RUN.json` binds the exact source/object, 223 loaded local dependency modules,
full printed types, definitions, assumptions, and frozen specification inputs.

The audit commands are `python3 -B proof-work/secp-square-execution/verify.py`
with `compile`, `kernel`, or `check`, run from the repository root. The first
two are one-shot operations: poll their original processes, rather than
launching duplicate compilers. Only a completed `CHECKED.json` and matching
recursive kernel log establish success of the kernel stage; a launch record
does not. The receipts are specific to their recorded trees and exact inputs,
not a portable clean-checkout build claim.

Remaining obligations are substantial: connect the actual symbolic C limbs
to the square modulo the field prime under the reader's bounds, prove the
representation/range facts needed by the writer, and compose the real public
reader, helper, writer, return, and local-memory lifecycle. Keep the original
C and literal specification fixed. This packet adds zero accepted coverage.
