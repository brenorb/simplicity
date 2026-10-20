# Full-input original readers, multiplication, and writer

`FieldInput.Compose.eval_original_read_pair_mul_write` starts from the
encoded **full Word256 pair**, a valid output frame, three distinct owned
caller-local objects and their initial source-frame fields. It proves four
actual original C calls in order: `read_fe(&a, &src)`, `read_fe(&b, &src)`,
`secp256k1_fe_mul(&a, &a, &b)`, and `write_fe(dst, &a)`.

The multiplier's limb bounds and initial ten-variable representation are
derived from the actual reader results. They are not premises of this final
theorem. The inputs may be any Word256 values, including at or above the
prime: normalization in each real reader preserves the product modulo the
field prime. No helper execution or output fact is assumed.

The final output has the existing `finv` encoding/cursor/memory contract for
`input_product_word x y`, the raw input product modulo the unchanged prime.
All three local objects remain Freeable for cleanup; the shared local source
frame has advanced by exactly 512 bits. Outside-local/non-external framing
is composed through all four calls. The output capacity requirement is 256
bits; the source cursor has the corresponding 512-bit representability bound.

This is **not yet the public jet's literal Simplicity equivalence**.
`input_product_word` is a numeric intermediate, not a replacement
specification. Remaining: connect the literal multiply/modulo program and
assemble the actual public `f_simplicity_fe_multiply` body with entry, source
copy, return conversion and all three final frees. Do not register this
helper chain as a complete public theorem.

## Reused structure and verification

`Input` reuses the existing canonical reader normalizer, `limb_rho_unsigned`,
`fe_limbs_of_ok` and region constructors. `Reader` reuses the actual symbolic
reader execution and its canonical field collector while additionally
deriving the current source cursor from the returned representation.
`Pair` keeps the first field through the second read and preserves both
fields' storage. `Compose` supplies the checked multiplier/writer theorem's
entire entry contract and retains source-frame storage through it.

The first composition experiment completed its tactics and had no remaining
goals/evars, but closing the proof hit the ten-second budget. Keeping the
named arithmetic/program models opaque made the complete file compile in
under a second, without increasing that budget or weakening the statement.
Retain this opacity when specializing the large multiplier model to reader
outputs; do not eagerly unfold `pair_rho`, normalization, or encodings.

Next use `literal_fe_multiply` and its checked correspondence/numeric bridges
from the pending negation work, rather than redefining the specification as
integer modulo. Reuse the existing public-copy/lifecycle lemmas, extending
their two-local allocation/free pattern to the real three-local function.
All legitimate input and frame layouts must remain supported.

The actual entry allocates the source copy, `a`, and `b` before performing
the source-frame copy. Do not place the third allocation after the existing
two-local copy helper: that would change the Clight action sequence. Reuse
the underlying allocation/framing, `frame_loadbytes_at`, and source-copy
lemmas in the extended three-local environment. Compute `blocks_of_env` for
that environment instead of assuming its free-list order.

Original C, canonical specifications, API, generation settings, main proof
sources, registry and unrelated staged patch are unchanged. Public coverage
added: zero.
