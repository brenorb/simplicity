# Token amount: checked compound-initialization building block

This is **not a completed token-amount jet equivalence proof**. It addresses
the additional C-local-memory work absent from the asset-amount getters.

`issuanceTokenAmt` writes an optional amount. For new issuance it passes
`issuance->tokenAmt` to `amt`; for reissuance it creates a local `confAmount`
with explicit value zero and prefix EXPLICIT, then passes that local object.
Its local allocation and free mean the tag-only asset helper cannot simply be
renamed or applied to this function.

## Completed helper

Private tree: `/private/tmp/jet-elements-token-amount.unLYUV`, cloned only from
the completed issuance asset-amount proof tree. Its only new source is
`C/jet_elements_token_zero_init.v`, archived under `source/`.

Five results and four definitions establish the actual AST fragment, local
object/union/prefix addresses, both typed stores and their composition.
`exec_token_zero_init` derives a memory satisfying `amount_rep ... (Explicit
Int64.zero)` from writable local storage. It preserves loads outside that
object, permissions and valid blocks. It does not assume either store executes
or the desired resulting representation. Only the two fields actually read
by the explicit-amount helper are initialized; unrelated bytes/padding are
not assumed zero.

Checker1117 and independent evidence review both terminated with exit0:
fresh compilation, full type/definition and assumption reports, the generated
Elements AST check, and recursive kernel checking passed. The AST-fragment
equality is closed. The final store-sequence execution result retains the six
inherited Coq/CompCert assumptions; address lemmas retain the four inherited
standard-library assumptions. `ZERO-INIT-CHECKED.json` binds the completed
commands, source, fresh object and logs; `ZERO-INIT-REVIEW.json` verifies them.
No normal registry or main source was changed; coverage added is zero.

## Remaining implementation-to-specification chain

1. Prove the actual `f_issuanceTokenAmt` entry/allocation, tag dispatch,
   field-pointer selection or local-zero initialization, `amt` call, and free.
   Establish local-object/frame disjointness from fresh allocation and retain
   the original input loads through frame writes.
2. Instantiate the shared indexed wrapper and current-input wrapper for the
   real token-amount functions. Keep every memory/execution obligation in the
   derivation, not as an additional final premise.
3. Link the results to the canonical `IssuanceTokenAmount`: optional issuance,
   new-issuance token amount, **explicit zero on reissuance**, then the shared
   Word64 confidential encoder. The current program asserts that primitive at
   `CurrentIndex`.
4. Freshly compile and recursively kernel-check the complete endpoints;
   independently review canonical correspondence, assumptions and full types;
   only then prepare normal registration and full acceptance.

Use the pinned normal CLI through `elements-count/support.py:s.ENV`. Do not mix
the separate interactive MCP backend's OCaml4.14.1 objects with this normal
OCaml4.14.4 build. The every-jet goal and this token family remain unfinished.
