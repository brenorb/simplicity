# Precise readonly framing for original internal C calls

Follow-up: `../secp-beta-public/README.md` records the stronger readonly
preservation theorem and complete public beta proof. Its separate exact-input
receipts determine completed verification; this packet's checked proofs and
historical evidence remain unchanged.

This packet closes the multiplier-helper framing gap recorded in
`../secp-beta-global/README.md`. It does not yet prove or register the whole
public `FeMultiplyBeta` jet. All original targets stay fixed; coverage added: zero.

`Internal.v.source` defines a small static checker for a closed set of direct
internal function calls. Its generic proof covers assignment, temporaries,
sequences, conditionals, loops and returns. Builtins, unknown/indirect calls,
switches and labels are rejected; this restricts where the checker applies,
not the input domain of any accepted C execution. The actual multiplier's
entire reachable set is checked and satisfies it.

The proof also establishes that actual local allocation cannot shadow a
function-typed global callee: `plain_env` is derived from the real Clight2 entry
and checked local types. `internal_table_ok` is a premise of the reusable
generic theorem, but is fully discharged for the original multiplier, not
passed as an assumption to the actual execution endpoint.

`Multiply.v.source` checks the original eight-function closure: `fe_mul`,
`fe_mul_inner`, `u128_mul`, `u128_accum_mul`, `u128_accum_u64`, `u128_rshift`,
`u128_to_u64`, and `umul128`. Symbols and internal function definitions use
existing linkage proofs, never substituted implementations or block-number
premises. It derives final beta readability from the actual borrowed output
representation, then proves full load/permission framing and preservation of
the initialized-global invariant.

`Observed.v.source` composes this with the already checked actual multiplication
call. The new endpoint `eval_beta_with_precise_frame` executes original C, derives
the existing writer's input representation and retained local ownership, keeps
beta initialized, and frames **every other block**. No disjointness condition
between the public input and beta global is introduced. No inference from five
word loads to arbitrary byte/fragments preservation is made: full framing
comes from the proved execution property.

The new 17-result audit has eight closed results, four with the four inherited
classical/extensionality assumptions, and five with the same six inherited
Coq/CompCert assumptions. In particular, none uses
`external_functions_properties` or `inline_assembly_properties`. The three
unchanged existing readonly-support modules are freshly compiled and bound in
the loaded source/object inventory. Some other exported theorems in those
modules do depend on the two properties; these new proofs do not use them.

## Next: complete the public beta jet

Use `eval_beta_with_precise_frame` to preserve `invA` through multiplication
using separation from **only the writable local**, then invoke the existing
bounded-limb `write_fe` theorem and `beta_product_matches_literal`. Compose the
actual `read_fe`, source-copy, two-local entry/free and return. The original
field normalization lifecycle (`C.jet_secp_public_lifecycle`) has the same
16-byte source and 40-byte field locals; the scalar lambda lifecycle is only
a structural reference (its field local is 32 bytes, so do not copy its layout).

The original whole public beta call graph has 20 internal functions, with no
missing direct callees in the inspected generated AST; the writer alone has
seven. This is an inspected inventory, not yet a checked table for those roots.
The static checker can be instantiated for them as needed.

A useful stronger shared invariant for startup preservation through arbitrary
internal-only stages is `mem_forward m mf` together with
`Mem.unchanged_on (fun b ofs => Mem.valid_block m b /\
  ~ Mem.perm m b ofs Max Writable) m mf`.
Store/storebytes/alloc/free lemmas already provide the raw unchanged facts.
Compose them using maximum-permission monotonicity and the **initial-valid-block**
condition; omitting that condition would incorrectly include freshly allocated
blocks in a transitive readonly footprint. Reuse the generic closed-callgraph
induction for this stronger invariant if intermediate beta readability would
otherwise have to be recovered from insufficient observations. This stronger
invariant is a proposed next proof, not a result of this packet.

Finally prove the full initialized local contract and its framing obligations,
audit the literal source correspondence, and only then attempt registration
and full acceptance. Unrelated frozen Bitcoin failures are not solved here.
