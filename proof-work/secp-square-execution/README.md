# Original optimized C square: execution foundation

This packet proves execution of the original `secp256k1_fe_sqr` wrapper and its
optimized squaring inner routine. It does **not** yet prove equivalence of the
public `simplicity_fe_square` jet to its Simplicity specification.

`eval_original_square_owned_inplace` establishes an actual Clight call with
identical input/output pointers, a five-limb owned output representation, and
memory framing outside that region. Its symbolic output comes from the real
optimized squaring code, not a substituted multiplication implementation.
The module also records the literal specification wiring and its numeric
meaning. Those specification lemmas alone are not C-to-specification proofs.

Remaining obligations are substantial: connect the actual symbolic C limbs
to the square modulo the field prime under the reader's bounds, prove the
representation/range facts needed by the writer, and compose the real public
reader, helper, writer, return, and local-memory lifecycle. Keep the original
C and literal specification fixed. This packet adds zero accepted coverage.
