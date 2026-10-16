# Token amount: actual pointer selection and armed-branch execution

Private tree: `/private/tmp/jet-elements-token-select.BDJBNs`, cloned from the
completed local-initializer tree. The only new source is
`C/jet_elements_token_select.v`, archived in `source/`.

Seven results and eleven definitions now compile and recursively kernel-check:
the exact selection/armed AST fragments; the new-issuance union's token amount
address at offset32; selection of either that address or the local explicit-zero
object; the actual amount call; and the complete nonempty-issuance arm,
including its real tag reload, conditional, local stores when needed and call.

`exec_token_armed` derives the `amt` execution from the represented selected
amount and verified `amount_rep_runs`. It does not assume that call executes or
produces the desired cells. The result retains the actual frame and exposes
local initialization separately, preserving loads outside the local object,
permissions and valid blocks. This separation matters: writes to an allocated
local object cannot be hidden inside an output-only framing assertion.

Checker66371 and independent `review.py ... --record` terminated with exit0.
Fresh compilation, full type/definition and assumption reports, generated
Elements AST comparison and recursive kernel checking passed.
`SELECT-CHECKED.json` and `SELECT-REVIEW.json` bind source, fresh object, exact
commands, logs and reviewed evidence. Both AST shapes and the field-layout fact
are closed; the armed execution result retains the six inherited assumptions.
Main, both live full-audit trees and the user's original index were unchanged.

**No whole token-amount function or jet is claimed yet.** Allocation/entry,
the outer presence-bit dispatch, no-issuance padding, local free and final
framing composition still need to be connected to these checked pieces. The
generic indexed/current wrappers and canonical `IssuanceTokenAmount` bridge
follow that function boundary. Coverage added is zero; no normal registration
or full normal acceptance is represented by these helper receipts.

Next, preserve the initialization boundary explicitly while composing frame
writes, then discharge it from fresh allocation and the actual free. Do not
weaken the final write-effect contract, assume local-memory preservation, or
count a branch theorem as the requested jet-equivalence endpoint.
