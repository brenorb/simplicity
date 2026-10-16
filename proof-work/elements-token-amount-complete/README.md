# Original C issuance token-amount jets: checked literal contracts

Two more whole-C implementation-to-specification contracts are now compiled,
recursively kernel-checked and independently source/evidence-reviewed:

- `elements_issuance_token_amount_literal_local_spec`.
- `elements_current_issuance_token_amount_literal_local_spec`.

Private tree: `/private/tmp/jet-token-local-effects.ykOxUN`.
Input SHA-256:
`2de2c3326e6cbf4d6c59b1834e00604e205181bd588f18904352ed36b65e24d8`.
Four new modules are archived under `source/`: shared allocation/framing
composition, the complete static C helper, both jet wrappers, and literal
canonical bridges. The seed is the completed token-selection tree; no objects
were copied from either running full audit.

## The actual C-to-Simplicity chain

`eval_elements_issuanceTokenAmt` establishes the complete actual static helper
call: function entry, allocation of the40-byte compound object, issuance-tag
load, presence-bit call, all three branches, selected amount call or padding,
local free, and full output/memory framing. Reissuance uses an **explicit zero
amount**, not its asset amount or a token field. The initialized object is
derived from its writable allocation; it is not an extra representation or
execution premise.

The shared `write_effect_local_alloc` composes a presence bit, local-object
initialization and payload write, restoring the full write-effect contract
through the actual allocation/free operations. It is parameterized by object
size and payload width. The final helper instantiates it, discharging its
memory-operation premises. This avoids weakening loads-outside-output framing
to hide the local stores.

The indexed and current jets reuse the existing verified pointer wrappers,
then the Word64 confidential encoder, generic indexed-value lemma and current
primitive transport. They preserve the original frame/cursor/memory contract,
not just the output value. The representation loads the issuance tag and the
new-issuance token amount only when that branch is present. No cached token
amount is required for reissuance because C constructs zero locally.

The literal specification follows Haskell `IssuanceTokenAmount`: Word32
index/list routing, optional issuance, `newIssuanceTokenAmount` for new issuance,
and `const (Amount (Explicit 0))` for reissuance, with proof data cleared and
unsigned Word64 encoding. The current program is `CurrentIndex >>> assert
(primitive IssuanceTokenAmount)`. The source guard checks these exact Haskell
clauses, Coq port and literal definitions, four whole-C statements and all three
relevant C bodies, reusing the prior amount/issuance encoder guards.

## Completed checks

Checker12698 terminated with exit0: all four new modules freshly compiled,
24 full result types and16 definitions reported, the Elements AST compared,
and the four modules recursively kernel-checked. Nine results are closed.
Both canonical-Coq endpoints and both literal endpoints retain exactly the six
inherited Coq/CompCert assumptions, without a new libc, execution, success or
desired-output premise. Full reports, source/object hashes and exact command
exits/logs are bound by `CHECKED.json`.

Independent finish45508 terminated with exit0. All49 source corruptions and40
proof/evidence/object/kernel-scope corruptions were rejected.
`EVIDENCE-REVIEW.json` binds the completed checker, source, all five tools and
three successful review commands/logs. The main407 source, live415 audit tree
and user's original index were unchanged. This is not normal registration or
full normal acceptance; coverage added by this proof receipt is zero.

## Next normal-registration boundary

No417 candidate or full audit is claimed. Normal registration must include
the **two earlier unregistered helper modules** as well as these four: zero
initialization (`../elements-token-amount/`) and selection/armed execution
(`../elements-token-select/`). Across the six modules there are36 results and31
definitions; their dependency/source/object evidence resides in the three
completed, separately bound receipts. Preserve all six sources and review
their combined declaration/assumption inventories rather than silently leaving
helper declarations out of the audit.

Do not edit main407 or the isolated415 candidate while their full audits run
(handles37961 and63601). Future415 installation first requires both real full
successes and a guarded source-only delta. The token proofs can be prepared as
a separate successor without modifying either live audit tree.

The inherited caller/environment and empty-array pointer domain remain
explicit, as do host-library/cryptographic fidelity and LP64/RECKLESS scope.
These proofs do not establish real environment construction, secp field
arithmetic or another build configuration. The every-jet goal remains
unfinished, including the104 existing `memcpy_model` conditions. Receipts bind
the actual preserved dirty/staged base, not clean-HEAD reproducibility.
