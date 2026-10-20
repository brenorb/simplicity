# Original in-place scalar multiplication caller body

Four checked modules prove the **whole unchanged scalar_mul C body** for the
public multiplication jet's actual `r=a` alias. Starting with its legitimately
allocated local product array, uninitialized output is supported. Both actual
helper calls, their current-memory interface, the exact product modulo the
canonical group order and outside-region framing are derived.

This is an internal **body** theorem, not a full caller function or a public
C-to-literal-Simplicity jet theorem. It adds **zero** registered jets.

## Checked roots and scope

- `eval_scalar_mul512_fresh_product`: original full product-helper call,
  arbitrary initialized operands, uninitialized output buffer, all eight actual
  current-memory output loads, exact full 512-bit product and framing.
- `region_u64_transport`: reusable same-memory region reindexing/rho adapter
  with exact denotation maps; retains offsets, permissions and ownership.
- `product_reduce_entry_rep`: establishes the reduction's entry representation
  from the actual product's postcondition, in the **same current memory**.
- `eval_product_then_reduce`: both original full helper calls composed, with
  their real memory states, output representation, modulo identity and frames.
- `exec_scalar_mul_caller_body_inplace`: both call nodes in the unchanged
  original `f_secp256k1_scalar_mul` body. It requires only the allocated entry
  representation and actual r/a/b temp values. The destination pointer equals
  the first operand pointer; product scratch and the two operands are distinct
  owned regions.

The two statement-call adapters take executions as compositional premises,
but the **body root discharges both** with checked original helper executions.
Do not count those adapters or this body as public jet equivalence.

## Verification

Fresh explicit build of all four modules and both drivers exited zero.
The independent kernel check, started after the four proof-module rebuilds,
exited zero. Full untruncated types/definitions and exact dependencies are
hash-pinned. 22 results, eight definitions: 14 closed, two representation
results with the inherited four classical/extensionality dependencies, six
execution results additionally using the inherited two CompCert semantic
parameters. No new axiom. The kernel context is the inherited 15-axiom context
and all three unsafe categories are empty.

The read-only reviewer also checks frozen prerequisite milestones and the
compiled dependency fingerprint. Ten in-memory negative fixtures reject
status/source/contract/dependency/kernel/classification drift and false coverage.
