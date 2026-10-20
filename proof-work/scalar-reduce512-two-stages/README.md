# Checked actual first and second scalar reduction stages

The root proves execution of the **unchanged original generated body prefix
through p4**, not a handwritten substitute function or assumed phase call.
It produces all four actual Vlong digit temps and the actual Vint p4 temp,
the exact five-limb second-fold value, p4's untruncated bound <= 2, current
memory representation, temp agreement, and outside framing.

Its only entry conditions are the allocated owned-region representation,
actual initial parameter-temp agreement and local-environment agreement.
The intermediate checkpoint's representation, temp equalities, m6 range,
high-part bound and all fast-operation guards are **proved internally** from
the actual first fold. They are not added as caller assumptions.

## How the source/value/execution chain works

`typed_stage` extracts the actual statement slice between `_m6` and `_p4`
and proves exact reconstruction with the original first prefix. It runs this
slice with typed `XL` / `XI` machine-value leaves. `typed_atomic` proves that
all five resulting expressions are the factored source schedule, including
both real unsigned casts. Unlike the earlier monolithic second-fold run,
this finite slice does not repeatedly expand first-fold expression trees.

`typed_value` proves the mixed-column arithmetic, derives every fast guard
under explicit internal stage conditions, reconstructs the untruncated p4
value, and proves its narrowing lossless under the sharp high-part bound.
`typed_exec` uses the verified compact statement executor and original helper
table to prove actual Clight execution, actual raw temps and framing.

`checkpoint` derives the concrete typed temp leaves and numeric guards from
the checked first-fold representation. The original rho, concrete temp
environment and memory remain unchanged. `jet_sx_forget_cells` proves that
forgetting initialized cell values retains shape, permissions, separation,
ownership and the region invariant. The first two owned regions retain their
actual initialized values; only the scratch locals' logical cell values are
forgotten. The checked second-stage run verifies stores before any reads of
those cells. No concrete memory is erased or replaced.

`two_stages` derives actual first-prefix execution, establishes the typed
checkpoint in that resulting memory/environment, executes the original second
slice, and recombines the exact statement spine with
`exec_statement_prefix_then_last`. The complete first/second computation is
independent of the giant monolithic second-prefix SX output.

This is still an **internal body-prefix theorem**, LP64 / RECKLESS, on the
original owned allocations. Actual whole-function entry, remaining third/final
reduction, return/local freeing, public multiply/square lifecycles, arbitrary
evaluator frames and literal canonical Simplicity equivalence remain open.
No public specification is replaced, no registry changes are made, and no new
public coverage or full acceptance is claimed.

## Verification

From the dependency Coq directory, pinned Coq 8.17.1 on PATH, stack 65520 KiB:
