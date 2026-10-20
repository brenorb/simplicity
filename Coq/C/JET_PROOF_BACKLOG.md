# Remaining jet proof work

The current local-contract registry contains 432 of the 533 header declarations.
The recently completed registrations and their conditions are listed in
[JET_ACCEPTANCE.md](JET_ACCEPTANCE.md); 101 declarations remain unregistered.

The remaining work includes:

- shared frame-domain and evaluator admissibility;
- exhaustive inherited correspondence to canonical programs;
- general caller startup and persistent SHA/global-state readiness;
- libc implementation proofs where a contract assumes `memcpy_model`;
- raw transaction/taproot projections for cached Bitcoin environment fields.

[JET_INHERITED_REVIEW.md](JET_INHERITED_REVIEW.md),
[JET_FIDELITY_REVIEW.md](JET_FIDELITY_REVIEW.md) and the `JET_*_MISMATCHES.md`
reports describe these boundaries. Production C, canonical Haskell and the
frozen `Coq/Simplicity` model must not be changed to make a proof pass.

Unique earlier candidates, diagnostic witnesses, derived trees and the parallel
field multiplication/square alternative remain in `../../proof-work/`, outside
the active build. See its README for recovery instructions and archive limits.
Their presence does not register or accept additional jets. Current acceptance
is reproduced with `bash Coq/check-jets.sh --accept`; old run records and
continuation journals are not required.

## Completed: `simplicity_gej_rescale`

`C.jet_secp_rescale_local.gej_rescale_literal_local_spec` now proves the
complete original public jet against the literal canonical Simplicity tree.
It covers unrestricted Word256 coordinates and scale (including zero), the
standard local-frame contract, actual reads and writes, return value and
local frees. No curve, nonzero, initialized-global or libc-model premise is
added. Its registration passed ordinary scoped acceptance, including all 291
kernel-checked dependency modules, reviewed assumption/contract comparisons,
negative tests and all five AST regenerations. Reproduce with
`bash Coq/check-jets.sh --accept --jets=simplicity_gej_rescale`.

The separate-output square support is now in the ordinary
`jet_secp_square_separate_{layout,exec,numeric,caller}.v` modules. It executes
the original helper into an uninitialized, distinct destination, preserves
the input and allocation permissions, and reuses the selected square proof's
arithmetic and literal-specification bridge. It is not a second registration
of `fe_square`.

`jet_secp_rescale_prefix.v` proves execution of the first two statements of
the actual helper body: the retained `fe_is_zero` check loop and the square
into local `zz`. The numeric endpoint preserves the scalar field, the point's
128-byte allocation permissions and `zz`'s 40-byte allocation permissions,
and supplies the square value and reusable limb bounds. There is no nonzero
scale premise. These are prefix/helper results, not a completed jet contract;
these prefix results alone did not increase coverage.

`jet_secp_rescale_entry.v` constructs the input representation from concrete
caller storage and proves actual function entry, parameter binding and fresh
`zz` allocation. `jet_secp_rescale_start.v` composes this with the prefix:
`rescale_start_from_storage` supplies the square result, reusable bounds,
preserved scalar and allocation permissions, all loads/permissions in the
original point block, and framing outside the caller's point/scalar blocks.
No initialized square destination or intermediate execution is assumed.

The `jet_secp_point_mul_{run,storage,numeric}.v` modules now execute actual
`fe_mul` calls at every point-coordinate offset while retaining ownership
of the whole 128-byte point. `eval_point_mul_numeric` derives execution,
the modular product, reusable bounds, source-field preservation and framing
from concrete caller storage. Its u128 event witnesses are discharged,
not caller premises. The shared `jet_secp_u128_word_*` and
`jet_secp_field_mul_word_*` modules adapt the archived independent helper
proofs, without registering alternative field jets. Their numeric model
uses the C routine's 56-/52-bit operand bounds: normalized-only 52-/48-bit
bounds would not follow from the square contract's 49-bit top-limb bound.

`jet_secp_point_mul_preservation.v` derives other-coordinate, flag and
third-block preservation. `jet_secp_rescale_calls.v` chains the four actual
callee executions; `jet_secp_rescale_statements.v` connects them to the four
original `Scall` nodes, using the existing generated-layout facts and proving
the local/global address evaluations. `jet_secp_rescale_owned.v` now proves
`eval_gej_rescale_owned`: actual entry, all six original body statements and
the final `zz` free, with exact output limbs, reusable bounds, unchanged
scalar/flag, retained caller ownership and external framing. This is the
complete **internal helper**, not the public jet-to-literal-specification
contract, and it does not increase registered coverage.

With the documented Coq 8.17.1 toolchain and matching pinned dependencies,
reproduce the focused build and recursive kernel check with:

```sh
JET_TARGETS=C/jet_secp_rescale_local.vo bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_rescale_local
```

The kernel command enables the checker's supported VM conversion; it still
recursively checks every imported module, without admitting dependencies or
disabling kernel checks. The ordinary acceptance command remains unchanged.

`jet_secp_rescale_literal.v` ports the original Haskell `gej_rescale`, `zinv`
and cube trees. `rescale_reader_outputs_literal` connects all three helper
outputs through the existing wide field writer's value function to that
literal program for unrestricted Word256 inputs. It discharges the residue
premises from the normalized reader representation, including the difference
between C's two Y multiplications and the specification's cube expression.
This value bridge is composed with actual serialization by
`jet_secp_rescale_writer.v`, reusing `eval_write_gej_general`. The
`jet_secp_rescale_public_{entry,body,prepare,reads,call}.v` modules derive the
original three-local entry, source-frame copy, four reads, helper call,
writer call and frees. The final local endpoint uses the existing
`secp_jet_local_spec`, not a rescale-specific weakened contract.

The checked rescale closure uses the declared Coq 8.17.1 baseline (the Nix
compiler built with OCaml 4.14.4). The older reader/writer dependency closure
was rebuilt from source in a clean temporary tree under that baseline, then
the complete endpoint was rebuilt through the normal project target. No
compiler or dependency pin was changed to match older OCaml 4.14.1 caches.

`secp-field-integration/check-rescale.py` compares the actual catalog, GEJ/FE
types, Haskell rescale/cube/zinv trees, literal port and exact final contract;
12 targeted mutations are rejected. It supplements rather than replaces the
formal execution proof and is included in the ordinary acceptance command.

Coordinates live at offsets 0, 40 and 80 inside
one owned 128-byte point allocation. The existing owned multiply contract
requires each owned region's base to be zero; it cannot directly represent
a fictitious 40-byte allocation at offset 40 or 80. Reuse the whole-point
region pattern in `jet_secp_point_write_run.v` when extending execution
support. Claude's checked u128 helper oracles remain available in the
parallel-proof archive if needed; do not register the alternative
`fe_multiply` or `fe_square` endpoints as well as the selected ones.

## Completed proof: `simplicity_sha_256_block`

The complete C execution theorem in `jet_sha_block_local.v` and the
startup-invariant/preservation adapter in `jet_sha_startup_jets.v` are reused.
The older Coq SHA program uses `Word.adder` where Haskell uses `Arith.add`;
the bridge uses `canonical_add_word_matches_adder`, not syntactic identity.
The original compression proof is not repeated, and global-state scope
remains explicit below.

`jet_sha_block_literal.v` now has a shared block-tree template, a literal
`Arith.add word32 >>> ih` adapter, and a semantic equality to the older Coq
SHA program. `jet_sha_block_literal_local.v` composes that bridge with the
existing actual C execution theorem and the startup-state preservation
adapter; both local and persistent-startup contracts compile. The existing
SHA/startup dependency closure (including `sha_init_mem_exists`) was rebuilt
from source in a clean temporary tree under Coq 8.17.1/OCaml 4.14.4.

The literal constant-rotation and right-shift generators are now ported from
Haskell. Their SHA specializations equal the older Coq wiring in every Core
algebra, with closed program-equality proofs. The source-correspondence gate
compares the actual block Core trees, all 64 constants and reused word/bit
dependencies; 86 mutations exercise those checks and the exact public contracts.
This supplements, rather than replaces, the kernel-checked C proof.

The lifecycle endpoint derives dispatch from the existing caller lifecycle,
which starts at actual `Genv.init_mem` and preserves startup state through
owned memory operations and verified jet calls. Existence of this initial
memory/lifecycle is also imported and kernel-checked. The C dispatch pointer
is mutable: these results cover its initialized portable implementation,
not arbitrary externally installed optimized callbacks.

The registry selects the complete local contract with `sha_dispatch_ok`, not
the stronger startup/lifecycle preconditions. Ordinary scoped acceptance
passed the 264-module kernel closure, reviewed snapshots, negative tests and
all five AST regenerations. Reproduce it with
`bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block`.
The old C compression and reader/writer proofs are reused rather than reimplemented. Focused builds use
`JET_TARGETS=C/jet_sha_block_literal_local.vo bash Coq/build-jets.sh -j2`.
The candidate and actual initial-memory existence proof passed recursive
kernel checking with
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_sha_block_literal_local C.jet_sha_startup_init`.
The local endpoint inherits six assumptions and the stronger startup/lifecycle
endpoints eight, all within the existing Coq/CompCert allowlist. The two
startup/lifecycle variants are supporting results, not additional entries.
