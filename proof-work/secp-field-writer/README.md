# Real multiplication followed by the original writer

`FieldWriter.Call.eval_original_field_mul_then_write` starts with the
multiplier's two owned fields, its internal limb bounds, the existing output
frame invariant, and separation of the local fields from external frame
blocks. It proves actual original C calls to `secp256k1_fe_mul(&a, &a, &b)`
and `write_fe(dst, &a)`, including the latter's internal normalization,
serialization and byte/frame writes. No execution or output is assumed.

The theorem returns the encoded product modulo `2^256 - 4294968273`, the
precise `finv` output/cursor facts, the unchanged second input, **both fields'
Freeable permissions for caller cleanup**, and framing outside the original
fields and external frame blocks. The writer's representation, magnitude
bounds and post-multiplication frame invariant are derived, not added as
new premises.

`product_word` is an intermediate numeric word result, **not a replacement
Simplicity specification**. This is not yet a public jet equivalence proof:
the two real readers, their internal-bound/representation bridge, the literal
Simplicity multiply/reduction program, and the public caller's complete
entry/local-copy/free lifecycle remain to be composed. Preserve the full
Word256 input domain; the original readers reduce inputs at or above the
prime rather than rejecting them.

## Reused original writer proof

The three currently untracked `jet_secp_write_fe_wide_*` sources were reviewed,
archived byte-for-byte in `inherited/`, and freshly compiled with their whole
additional local dependency closure. Their main-checkout originals were not
edited, staged or registered. The numeric proof tracks the normalizer's
branch, normalized limbs, get-b32 substitution and machine-byte interpretation;
the execution proof invokes the real `eval_local_write_fe`, preserving its
frame and Freeable-region representation.

49 additional local modules were force-built, not inferred from old `.vo`
files. `DEPENDENCIES.json` binds their source, object, command and log
identities and the checked normalization parent. The shared regex scanner
flags the original Bit Machine datatype constructor named `Abort`. No scanner
was changed: the dependency verifier permits that one inherited file only
when its bytes equal `91d89bac:Coq/Simplicity/BitMachine.v`, with exactly its
three constructor-name occurrences and no vernacular `Abort.` command.
All other added source files pass the ordinary proof-safety scanner.

## Verification

The report covers 16 reused writer results and 10 new adapter/composition
results, seven definitions. Exact dependency profile: 19 closed, five memory
results with four inherited classical dependencies, two execution results
with the six inherited Coq/CompCert dependencies. No new axioms or external
models are added. `RUN.json` binds fresh compilation and full printed
contracts/assumptions; `CHECKED.json` additionally binds a successful recursive
kernel check. A launch file alone is not success.

The exact loaded closure is 148 source-built local modules and 48 extension
modules, including the two new modules. The separately checked
`FieldNormalize.Call` endpoint is not imported here. Negative checks reject
an extra assumption and detect an unfamiliar module namespace.

```sh
python3 -B proof-work/secp-field-writer/dependencies.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-writer/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-writer/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-writer/verify.py check \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

These are separate launch/check phases. Poll live process handles; do not
restart a launched phase merely because its observation yielded. The sources
must remain frozen while a phase is running.

Next: establish `field_input_bounds` and the multiplier's initial representation
from the actual two reader results. Reuse `fe_limbs_of_ok` and the reader's
existing canonical-limb theorem. The public function has three local objects:
a 16-byte source-frame copy and two 40-byte fields; the two readers advance
that same copy by 256 bits each. Preserve the other field and frame-copy
storage through each call, with the whole 512-bit input and 256-bit output
capacity, rather than restricting public inputs to canonical values.

For the literal program, reuse `literal_fe_multiply` from the pending
`jet_secp_negate_literal_contract`, with `literal_fe_multiply_matches` and the
`canonical_fe_multiply` / `canonical_fe_normalize512` bridges, after their
source-bound verification and correspondence review. The literal version
retains the canonical addition calls in recursive division; do not silently
replace it with the older optimized division port or numeric modulo.
Then combine these calls with the real public caller's entry/freeing proof.

Production C, canonical specifications, API, generation settings, main proof
sources and registries are unchanged. Public coverage added: zero.
