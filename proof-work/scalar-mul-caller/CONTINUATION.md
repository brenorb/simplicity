# Continue from the original in-place scalar_mul body

Last verified declaration:
`MulC.jet_secp_scalar_mul_caller_body.exec_scalar_mul_caller_body_inplace`.
Four complete modules passed fresh explicit build, full type/definition and
assumption drivers and independent kernel checking. No open proof remains in
this archive. Public jet acceptance is still false.

## First next task: actual scalar_mul function boundary

The generated caller is **two Scall nodes**, with one local `_l : ulong[8]`
and three pointer parameters. Its public multiplication invocation is
`scalar_mul(&a,&a,&b)`, **not three disjoint parameter pointers**.

1. Start from two represented owned 32-byte operand regions a/b. Prove entry
   and parameter binding with r and a pointing to the same block; uniqueness
   is about parameter identifiers, not argument values.
2. Allocate the actual 64-byte local array with Mem.alloc / alloc_variables.
   Preserve operand representation across this allocation. Its cells are
   initially **None**: use `scalar_mul512_fresh_regs`, not the older
   initialized-output product entry.
3. Construct/reindex the body layout **[l,a,b]**, retaining the same rho and
   memory. `region_u64_transport` supports integer-cell relayout and exact
   value maps. Prove separation from the allocation freshness and the existing
   a/b ownership; do not assume entry representation or callability.
4. Instantiate the checked body under the actual local environment and bound
   r/a/b temps. Output layout is **[a,l]**, with represented current output and
   still-owned 64-byte product buffer. Product-to-reduce reindexing is already
   discharged by `product_reduce_entry_rep`.
5. Derive Freeable ownership of l from the actual postcondition, prove the
   original void return and actual free_list. Retain a's region after free with
   prefix/unchanged-memory lemmas; derive actual final-memory output loads.
6. Compose outside framing using the original caller-memory validity guard
   across fresh allocation/body/free, as in the checked reduction function.
   Avoid requiring that fresh local blocks be unchanged. Required execution,
   free and post-memory facts must not become premises on the full root.

## Square is a distinct alias case

Public square invokes `scalar_mul(&a,&a,&a)`. The current product contract
uses **distinct owned operands**. Do not duplicate an owned region twice and
claim its separation, and do not infer that support for r=a implies a=b.

Prove a same-input product variant with body layout [l,a], both product helper
arguments pointing to a, and rho/value adapters duplicating the four input
limbs in the numeric product. Reuse checked column arithmetic and reduction
after a formal source/denotation bridge. The actual C caller/body is unchanged;
there is no separate scalar_sqr helper to invent.

## Public implementation-to-specification closure

Then compose the public readers, scalar normalization, in-place caller,
writer, return and local frees under general evaluator-frame contracts.
Keep both original raw inputs and close the result against the **literal**
`canonical_scalar_multiply`; square's literal Haskell program is
`iden &&& iden >>> scalar_multiply`. Numeric modulo adapters are internal
proof bridges, never replacement public specifications.
The immutable dependency base already contains literal normalization and
multiplication ports. Validate actual input/cast/carrier and output encoding
equalities, including current-memory preservation.

## Diagnosed issues from this milestone

- The old product proof assumed initialized scratch output; freshly allocated
  local memory does not provide those XLv values. A new compact run with None
  cells now proves the same output while preserving the original implementation.
- Comparing the entire fresh symbolic state with the entire old one timed out.
  The minimal closed completeness test passed. The successful decomposition
  proves fresh run completeness/selection, **only output-region equality**,
  actual return-temp and log facts separately. No longer timeout or unchecked
  cast was needed; giant irrelevant temporary trees need not be equated.
- Selective `cbn [Nat.ltb]` leaves small closed comparisons if Nat.leb is
  still folded. Include Nat.leb or isolate those constants; never normalize
  symbolic column machine operations just to reduce the comparison.
- Coq 8.17.1 has no `nth_error_nil` under these imports, and nth_error recurses
  on the index. Use the checked `empty_region_index` or destruct the index.
- Specify xs/ys/rho/beta explicitly when transporting a concrete u64 region.
  Inversion may already expand its cells; unification cannot infer the list
  passed to u64_cells from an evar alone.
- `repeat split` decomposes interval pairs too. Build the foot conjunction
  explicitly; the range fact then transports definitionally.
- AST.Internal is not Ctypes.Internal. The bridge uses the latter explicitly.
  Import defining modules for int_table, column_words_value, carrier values,
  machine-list length and Clightdefs notation; consumers do not re-export them.

Earlier whole-reduction function proof and all source/receipt files remain
frozen in `../scalar-reduce512-final`. Do not restart monolithic reduction
experiments. Preserve unrelated SHA/range/field-negate changes and the pending
scalar-add integration. Claude reserves Elements foundation/getters and shared
memcpy/SHA/constructibility; no overlap. Signed atomic local commits, no pushes.
