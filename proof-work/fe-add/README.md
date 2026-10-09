# Field addition: complete compiled public candidate, not registered coverage

Twenty-six exact source modules are preserved by `manifest.json`. They reuse the
checked symbolic-execution interface and owned-region contracts from negation,
not an altered C implementation. The two input regions represent the public
jet's separately allocated fields; this helper contract does not claim all
possible aliasing modes of the standalone C helper.

## Completed facts

Current endpoint: `fe_add_literal_local_spec`, the complete original-C public
contract against the literal port, with allocation/source copy/read/add/write/
return/free derived over arbitrary Word256 pairs. It compiles with six inherited
execution assumptions and no `memcpy_model`. The archive has 63 results.
Independent public kernel check 91932 passes with `-o`, exact inherited axiom
allowlist and no unsafe flags. The new source gate passes 52 negative fixtures,
with reused arithmetic/foundational gates also passing. Two checker sources are
archived alongside the proofs. Snapshots, full acceptance and integration remain
required for registration.
See `CONTINUATION.md`; helper receipts below are historical.

- `eval_field_add_from_owned_region` derives the actual original
  `f_secp256k1_fe_add` call, final representation, unchanged region shape and
  outside-memory framing from two owned field representations. Initial field
  storage retains Freeable metadata for later public cleanup.
- `eval_field_add_with_values` derives all five actual output loads, each the
  machine sum of the corresponding input limbs, together with that real call
  and representation/framing. It assumes neither execution nor output.
- `add_value_unsigned` proves exact non-wrapping integer sums for the reader's
  52-bit limb bounds. `add_value_wide_bound` places them below the existing wide
  writer's `2^60` bound. Both final numeric results are closed.
- `eval_field_add_owned` composes the two-region execution from initial
  `fe_at` fields and Freeable storage, deriving the real call, result field,
  both locals' Freeable permissions and outside-memory framing. It assumes
  neither execution nor output. Its representation adapter is parameterized
  over the initial limb-variable index, rather than duplicating one-field
  proofs for the second operand.
- `field_add_values_sum` proves the actual five-limb output denotes the sum of
  the two initial field representations. Its final equality is closed. This is
  an implementation representation bridge, not a substitute canonical program.

Helper and values modules freshly compile and pass independent whole-chain
kernel checks (43499 and 15503); both have exactly the 15 inherited library
axiom names, with no unsafe flags. The numeric module freshly compiles (76282).
Its independent whole-chain kernel check passes with exit 0 (95413), with
exactly the same 15 inherited library axioms and no unsafe flags. Storage,
initial-region and owned-composition whole-chain checks also pass with exit 0
(62130, 22804, 80818), with the exact same axiom allowlist and no unsafe flags.
The first six modules' sixteen results are kernel-checked. Two further modules
(`field_add_writer_bridge` and `literal_add_program`) freshly compile and pass
independent whole-chain kernel checks (12352, 43323), bringing checked support
to eight modules and twenty-two results. The literal numeric interpretation
and exact writer-to-literal equality freshly compile (five further results),
and pass independent kernel checks with exit 0 (89375, 6608), with the exact
inherited axiom allowlist and no unsafe flags. Thus all ten archived modules'
twenty-seven completed results compile and are independently kernel-checked.
These ten historical helper modules alone did not prove a public jet theorem.
Scratch root:
`/tmp/jet-fe-add-next.3vEywc`; logs
`kernel.log`, `values-compile.log`, `values-kernel.log`, `numeric-compile.log`,
`numeric-kernel.log`, `storage-kernel.log`, `initial-kernel.log`,
`owned-kernel.log`. Dependencies are the independently accepted reconciled
range tree at `/tmp/jet-range-consumer.RbIhbg/Coq`.

Further progress: the combined reader environment and normalized-owned helper
chain freshly compile and pass independent kernel checks (15388, 85088), adding
eight results. They discharge the intermediate bounds/value facts for arbitrary
raw Word256 pairs and derive the real helper call plus literal output equality
from the stored normalized fields. Read-invariant rebasing and first-field
preservation across the second reader also pass independent checks (78434,
84026). The actual source-frame loads pass kernel checking (34151). Reader-call
and strengthened two-reader contracts pass kernels 65630 and 17577. Pair-input
slicing and actual add-helper-plus-writer composition also pass independent
kernels (49538, 35616). Current total: nineteen modules/46 compiled and
independently kernel-checked results. Both raw reader memory frames are exported;
the canonical pair input derives both slices. See `CONTINUATION.md` for four-call
composition, source-copy preservation and the remaining actual public
composition. Output capacity is 256; 512 is input consumption.

Extract exact sources outside the repo with:

```sh
python3 proof-work/manage.py --extract fe-add --output /tmp/UNUSED-EXTERNAL-DIRECTORY
```

From the dependency Coq directory, using the project's Coq 8.17.1 PATH and a
65520 KiB stack, compile in manifest dependency order: `jet_secp_field_add`,
`jet_secp_field_add_values`, `jet_secp_field_add_numeric`,
`jet_secp_field_add_storage`, `jet_secp_field_add_initial`, then
`jet_secp_field_add_owned`, `jet_secp_field_add_writer_bridge`,
`jet_secp_literal_add_program`, `jet_secp_literal_add_numeric`, then
`jet_secp_add_literal_writer`, `jet_secp_add_reader_environment`,
`jet_secp_add_normalized_owned`, `jet_secp_read_fe_rebase`, then
`jet_secp_field_read_preservation`, `jet_secp_read_fe_source`,
`jet_secp_read_fe_cursor_call`, then `jet_secp_add_two_reads`.
The modules after the original six additionally use the
checked but not yet accepted negation interfaces at
`/tmp/jet-negate-accept.ftWsqQ/Coq`; use that Coq dependency root for their
builds. Use a narrow
`-R /tmp/EXTRACTED-DIRECTORY C`, never map all of `/tmp`.

## Historical public composition boundary (now compiled)

The four-call composition now compiles as `eval_field_add_four_calls` from
canonical pair input and initial owned local storage, deriving all four actual
calls, literal output, all three locals' Freeable storage and outside-memory
framing. Its independent kernel check passes as 38991 (silent, without context
inventory). Statement sequencing and return, actual three-allocation entry and
exact free_list cleanup now compile too. Total compiled archive is twenty-three
modules/58 results, with twenty modules/48 already kernel-checked. Combined
rest/entry kernel check 59542 is live. Source-copy preparation and composition
of entry/body/return/free into the complete public contract remain open.

The actual public `simplicity_fe_add` body copies the by-value source, reads
two consecutive Word256 inputs into separate locals, invokes the original
in-place add helper on those locals, calls the original wide writer, and
returns true. The three-variable allocation/source-copy/entry/free lifecycle
must be derived. Existing one-field entry lemmas cannot simply be relabeled.

Canonical Haskell `fe_add` is `add256 >>> cond ((unit >>> one256) &&& iden)
((unit >>> zero256) &&& iden) >>> fe_normalize512`. Preserve that carry-expanded
Word512 combinator chain and its full Word256-pair input domain. This literal
port now exists, with closed parametricity proofs and a compiled numeric
interpretation. `add_writer_literal_output` compares the actual helper's limb
output with that literal program under intermediate normalized-reader facts;
it does not assume raw inputs below the field order. Its five-limb bounds and
two normalized values must still be derived from actual readers. Complete the
literal source gate and mutation tests, rather than substitute a numeric modular
addition as the specification. Derive the reader
normalization transport, writer output/prefix/cursor/framing and Freeable
storage for all locals. Only a complete checked public theorem, source review,
negative gates, reviewed snapshots and independent full acceptance can add
coverage. No registration is made here.
