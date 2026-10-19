# Actual field multiplication followed by normalization

`eval_original_field_mul_then_normalize` establishes two actual original C
function calls: `secp256k1_fe_mul(&a, &a, &b)` followed by
`secp256k1_fe_normalize_var(&a)`. From the multiplier's initial owned arrays
and implementation limb bounds, it derives the normalizer's writable memory,
alignment, loads and all five limb-bound premises. Neither execution nor
the output is an assumed premise.

The final first field contains the canonical limbs of the input product
modulo `2^256 - 4294968273`. The second input field is unchanged, and memory
outside the two original owned arrays is framed. The proof reuses the
existing normalizer theorem, rather than rewriting its original C code or
canonical specification. All four additional local dependencies were freshly
compiled from sources identical to the main checkout; their source, object,
command and log identities are recorded in `DEPENDENCIES.json`.

Two sources, twelve results, two definitions. The exact expected dependency
profile is six closed results, five memory results with four inherited
classical dependencies, and one execution theorem with the six inherited
Coq/CompCert dependencies. `RUN.json` records fresh compilation and complete
type/definition/assumption reports. `CHECKED.json` additionally records a
successful recursive kernel check; launch records alone do not show success.
The loaded closure must match the source-built provenance exactly: 99 local
sources and 47 extension modules, including these two.

```sh
python3 -B proof-work/secp-field-normalize/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-normalize/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-normalize/verify.py check \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

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
