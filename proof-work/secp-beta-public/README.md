# Complete original C beta jet against the literal specification

Ordinary-module follow-up: `../secp-beta-integration/README.md` records the
exact reversible promotion and fresh normal build. Its separate receipts
determine completed integration verification; this proof packet is unchanged.

The endpoint is
`BetaPublic.Local.fe_multiply_beta_initialized_local_spec`:

```coq
secp_jet_initialized_local_spec beta_initialized
  f_simplicity_fe_multiply_beta (Word 8) (Word 8)
  (@literal_fe_multiply_beta Alg.CoreFunSem).
```

This is the existing full initialized frame/memory contract, not merely a
numeric helper result. The Word256 input is unrestricted; cursors and layouts
retain the shared contract's generality. There is no new nonalias condition on
the input, output or beta global. The initial beta state is explicit, follows
from the actual successful `Genv.init_mem jets_secp.prog` proved in
`../secp-beta-global`, and is preserved in the conclusion. No helper execution,
intermediate arithmetic output, final permission, or libc model is assumed.

The proof executes the unchanged original C entry, allocates its actual 16-byte
by-value source frame and 40-byte field local, performs the actual source copy,
`read_fe`, original `secp256k1_fe_mul` and inner body, actual normalization and
serialization through `write_fe`, return conversion and final local freeing.
It proves the literal specification's output, prefix/cursor facts and all
required preserved loads. The specification's `(beta,x)` order is retained;
the C helper's `(x,beta)` order is connected by the previously checked bridge.

## Reusable preservation

`Preserve` strengthens internal-only execution preservation to maximum-permission
monotonicity plus raw `Mem.unchanged_on` for initially valid readonly blocks.
Unlike readback alone, this preserves readability, exact permissions and raw
memory fragments without a final-readability premise. The initial-valid-block
condition makes composition sound across allocation. Store, storebytes, alloc,
free, actual Clight2 entry and assignment are proved cases, not model premises.

`Graph` kernel-checks the original complete twenty-function direct-call closure,
including reader, writer and every multiplication helper, using the prior
generic static-closure theorem. Unknown/indirect/external calls and builtins
cannot pass that checker. `State` derives beta startup preservation from it.
`Chain`, `Rest`, `Public` and `Local` compose the actual C calls and boundaries.
No generic external-call-properties theorem is used.

## Verification and scope

The authority remains the original frozen Haskell specification and generated C
program. The reviewed literal beta port and multiplication foundation are reused
unchanged. These checks do not establish Haskell compiler correctness, another
C architecture/build configuration, or full-repository acceptance.

This packet is a complete checked **unregistered proof candidate**. It does not
modify the pending shared registry, projects, snapshots or other staged work.
Accepted coverage added by this packet is zero. The unrelated frozen Bitcoin
identity/value-domain failures remain unresolved; no target corrections were
made to pass them. The every-jet objective is not complete.

## Next integration

Promote the exact checked sources to ordinary module names in an isolated
integration candidate, with reversible module-only renaming and a fresh normal
dependency build. Reuse the field-multiplication integration machinery, preserve
the full initialized contract and exact assumptions, and add a strict scoped
FeMultiplyBeta inventory check with mutation tests. Then review the registration
patch and attempt the full normal acceptance suite without bypassing the frozen
Bitcoin failures or disturbing the checkout's unrelated staged work.
