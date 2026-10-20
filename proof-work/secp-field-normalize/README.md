# Actual field multiplication followed by normalization

`eval_original_field_mul_then_normalize` establishes two actual original C
function calls: `secp256k1_fe_mul(&a, &a, &b)` followed by
`secp256k1_fe_normalize_var(&a)`. From the multiplier's initial owned arrays
and implementation limb bounds, it derives the normalizer's writable memory,
alignment, loads and all five limb-bound premises. Neither execution nor
the output is an assumed premise.

This is not the public multiplication jet's Simplicity equivalence. Its
reader-to-internal-input bridge, actual writer/byte/frame execution and
literal Simplicity specification bridge remain open. The final `fe_at`
contract exposes writable normalized limbs, not a restored stack-ownership
representation or a public jet's whole lifecycle. The unchanged original
writer performs normalization internally; this result is not a substitute
for composing that writer's actual execution.

Next: source-review and freshly verify the wide-writer chain before reuse,
then adapt the multiplier's exact output representation to the writer's
initial representation and frame invariant. The currently untracked
`jet_secp_write_fe_wide_*` sources belong to other pending work: they were
not edited or trusted as compiled dependencies here. Preserve all legitimate
256-bit public inputs: the original reader normalizes inputs at or above
the field prime rather than rejecting them. Establish the internal limb
bounds from that reader, not a new public-input restriction.

Original targets, generation configuration, API, main proof sources and
registries are unchanged. Public coverage added: zero.
