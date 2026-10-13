# Continue to the public scalar_multiply root

Last verified proof declaration:
`PubC.jet_secp_scalar_mul_write_chain.eval_scalar_mul_write_from_normalized_storage`.
The archive has completed proof sources, not an unfinished tactic prefix.
Fresh terminal verification is pinned in `REVIEW.json`. It is still an
intermediate caller theorem, not public jet acceptance.

The final target remains the unchanged public `simplicity_scalar_multiply`
against **literal** `canonical_scalar_multiply` under general evaluator frame
contracts. Do not replace that target with this smaller two-call sequence.

## First retain the second operand's ownership

There is already a **freshly compiled, not independently audited** extension
in `/tmp/jet-scalar-mul-ownership.Ste5AV` (namespace `OwnC`):
`jet_secp_scalar_mul_body_owned.v` and `jet_secp_scalar_mul_call_owned.v`.
They implement steps 1-4 below. Last compiler-checked declaration is
`OwnC.jet_secp_scalar_mul_call_owned.eval_scalar_mul_call_second_owned`;
both explicit builds exited zero (sessions 30154 and 74360). Body source SHA
is `b939029c71ef3f38e2cb857c056a0a3c6160f976540f2d49f18d7010af46295e`;
function source SHA is
`e96022e6eda9972a97b1c465556f3db212c3903e3f0d2e6f38c7c7325b000d97`.
These separate scratch modules were not inputs to this archive's kernel check
and are not counted in its 17 results. Audit their full types/definitions and
dependencies, rebuild and independently kernel-check before promotion. Do not
restart the ownership proof from scratch while those exact sources remain.

The previous complete function root exposes output ownership but drops b's
representation from its postcondition. Public cleanup frees both a and b.
Its outside-both-operands frame therefore cannot prove b Freeable.

The evidence needed is already available inside the actual call chain:

1. `eval_scalar_mul512_fresh` yields a post-product representation containing
   **all three regions** `[l,a,b]`, with b still owned. Retain that witness
   rather than relying only on `eval_product_then_reduce`, which discards it.
2. `product_reduce_entry_rep` constructs `[a,l]` in that same product memory.
   Original ownership separation gives b's block distinct from both a and l.
3. The actual reducer's `lframe` is outside `[a,l]`. Specialize its permission
   component to every byte of b's `[0,32)` region, using post-product validity
   and the two block inequalities. This derives Freeable ownership after the
   reducer; no new permission premise is allowed at the full root.
4. Carry that permission through the original caller's scratch free. Allocation
   freshness proves b differs from the freed l, so actual `free_list` framing
   preserves it. Retain both operands' permissions in a strengthened complete
   function/root interface, without editing older frozen receipts.
5. The writer preserves b because it is outside a's region and external blocks.
   Extend this archive's call-chain result to expose both final permissions.

Keep all conclusions tied to the **same** actual memories/executions. Do not
invoke two existential function theorems and assume their final memories are
equal, or assume the missing permission as a public premise.

## Compose the two actual readers

The pending scalar-add candidate already has the needed general two-reader
structure:

- `jet_secp_scalar_add_reader_support.v`;
- `jet_secp_scalar_add_two_reads.v`;
- `jet_secp_scalar_add_reader_environment.v` (the new reader bridge here
  reproduces its rho split while adapting multiplication's weighted value).

Read their exact statements and dependency names before reuse. They are in
`/tmp/jet-scalar-add-integration.RxsuOy/Coq/C`; do not modify its frozen tree or
evidence. Prefer shared promotion after isolated integration rather than
duplicating those helpers permanently. The generic writer source here is
already an exact reuse from that candidate.

The read/read composition must expose, in its actual final memory:

- scalar_at for normalized a and b, both Freeable regions;
- source cursor advanced by 512, and source-local Freeable permission;
- finv and at least 256 bits of output capacity;
- separation from external frame blocks;
- permitted memory changes/preservation of a while reading b.

These instantiate `eval_scalar_mul_write_from_normalized_storage` directly.
Do not leave its normalized-storage or numeric equalities as new premises of
the public jet theorem. Transport the source fields and ownership across
mul/write with the real lframe results.

## Finish the actual wrapper and evaluator result

Adapt the scalar-add public entry/body/lifecycle decomposition to the actual
generated multiplication AST: source struct copy, two readers, the void
scalar_mul call, writer, true return, three outer-local frees. Inspect exact
locals and call/result-temporary shapes; addition's integer helper result does
not transfer unchanged to multiplication's void call.

The composed result already uses
`encode (@canonical_scalar_multiply Alg.CoreFunSem (a,b))`; no modulo-only
replacement is needed. Reuse the existing canonical multiplication
parametricity bridge when closing the full evaluator contract. Ensure no
assumed entry, execution, output, free or invariant is smuggled into the
public root. Square still requires its independent `a=b` input-alias proof.

## Feedback/verification notes

- Alg's Core term notation conflicts with Translate's notation under these
  imports. Use `Require Simplicity.Alg` qualified when importing Translate,
  as the existing call-chain modules do.
- `two_region_rep_separate` is defined in `jet_secp_b32_exec`; import its
  defining module, not only consumers that mention it.
- Write the exact Z right-hand side in `change`; the unspecified `_` was not
  inferable in the numeric specification bridge.
- Declare the normalized-storage corollary **after** its underlying chain
  theorem. The archive's ordering is now correct.
- The root assumption audit traverses the full symbolic product/reduction
  dependency graph. It took considerably longer than the small new module
  builds, but completed within its 150-second process bound. Do not restart a
  live audit merely because an output-yield interval expires.
- The first independent kernel check reached its actual 300-second process
  deadline (exit 142, no diagnostic), not merely a tool observation timeout.
  A scoped process observation before that deadline showed active CPU use and
  about 2.6 GiB RSS. The unchanged closure was retried with a measured
  600-second bound; both attempt records/logs must remain visible in evidence.

Validate changed modules and full contracts/definitions/dependencies, then
kernel-check with sources frozen. Promote through an isolated reconciled
candidate and run integrated acceptance without update flags only after
review. These helper proofs add zero jets until the public root is checked.
Preserve unrelated dirty work; coordinate without touching Claude's reserved
environment/shared/Elements files. Keep the all-jet goal active. Signed local
atomic commits only, never pushes.
