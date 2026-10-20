# Token amount: actual pointer selection and armed-branch execution

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

Later progress: `../elements-token-amount-complete/` now contains the checked
complete helper, wrappers and literal endpoints. The archived receipt here
still certifies only its original selection/armed stage. Normal registration
and full normal acceptance of the complete token endpoints remain outstanding.
