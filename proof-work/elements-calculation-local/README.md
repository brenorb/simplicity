# Original calculation jets: enclosing C-to-Simplicity contracts

The three concrete theorems in `Local.v.source` target the unchanged original
Elements C jet bodies and the literal canonical `calculate_asset`,
`calculate_explicit_token` and `calculate_confidential_token` word programs.
The shared proof derives allocation, source copy, reader, helper call, returned
struct copy, writer, true return and all four frees from the initial frames.
It also derives output cells, destination cursor, prefix and outside-load
framing. No desired execution/output/cache premise is added to these endpoints.

The contracts remain conditional on `memcpy_model` and the initial compression
dispatch pointer, plus ordinary readable-input/writable-output frame premises.
They do not establish the libc model or actual startup/caller invariants.
There is no zero-initial-output or fixed-cursor restriction; all Word256 inputs
are quantified. The frame contract permits arbitrary valid word crossings.

Recovery (2026-10-18): the previous temporary trees disappeared after the
interruption. The five lifecycle modules were archived before that happened;
their original successful compile/reports and uncompleted kernel launch remain
intact in `../elements-calculation-lifecycle/`. The enclosing source here was
reconstructed and must be freshly rechecked, not certified by vanished objects.

This is an isolated, unregistered proof-support package. It changes no C,
canonical specification, API, generation settings, registry or normal gate and
adds zero accepted coverage. Full repository-wide jet equivalence remains open.
