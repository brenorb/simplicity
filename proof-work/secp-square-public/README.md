# Complete original public field-square jet

The endpoint is `SquarePublic.Local.fe_square_local_spec`:

```coq
secp_jet_local_spec f_simplicity_fe_square (Word 8) (Word 8)
  (@literal_fe_square Alg.CoreFunSem)
```

It proves the actual original public C jet in the existing secp Clight program,
not just its helper or a mathematical specification identity. The unrestricted
Word256 input is handled through the actual reader, the original optimized
square helper, and the actual normalizing writer. Entry, local allocation,
by-value source-frame copy, return value and local frees are also proved.

The theorem retains the existing general local-frame contract: valid source
frame/cursor, represented input bits, writable destination capacity, correct
output encoding, preservation of the output prefix, destination cursor update,
and preservation of unrelated loads. No beta-global readiness, assumed helper
execution, caller-supplied arithmetic conclusion, zero-output initialization or
new external-library premise is added. This has the same frozen generated
translation-unit/build scope as its checked dependencies, not a claim about
every architecture or alternate C build configuration.

## Structure and evidence

- `Chain` composes the three actual function calls and preserves the live
  frame invariant and both caller-owned local allocations.
- `Rest` proves the corresponding original statement sequence and return.
- `Public` supplies actual function entry, source copy and local frees.
- `Local` exposes the established public frame/memory contract against the
  literal Simplicity square program.

The private extension is `/private/tmp/jet-square-public.rLmhCR`, namespace
`SquarePublic`. It uses the checked `SquareCaller`, `SquareValue` and `SquareRun`
extensions on `/private/tmp/jet-beta-integration-qctc10_1`. The source-port
authority is the frozen original Haskell wiring already checked by the parent
packet; Coq proves the execution-to-literal-term result. No Haskell compiler
verification or target correction is claimed.

`verify.py compile` freshly compiles all four modules and prints all nine
result types, two definitions and complete assumption profiles. It also checks
the frozen-target guard, the exact endpoint/statement/callee wiring, twelve
negative source mutations, and the loaded dependency closure. `kernel` is a
separate one-shot recursive check; poll its original process. Only a terminal
successful `CHECKED.json` with the matching log establishes that stage.
`check` revalidates completed exact-input evidence. Run these commands as
`python3 -B proof-work/secp-square-public/verify.py <action>` from the repo root.
Launch records alone are not completion evidence.

All receipts are bound to their exact sources, compiled objects, parent
receipts, audit driver and main/staged inputs. They are not portable
clean-checkout build receipts. No proof skips, unchecked kernel conversions or
new axioms are used; the full endpoint retains the inherited assumption profile.

## Integration boundary

This is a full public-jet theorem, but remains **unregistered**. Accepted
coverage added by this packet is zero. Next assemble its exact source closure
as ordinary modules, freshly build it, and compare complete types, definitions
and assumptions under the module rename. Preserve unrelated staged work.
Normal registry acceptance must not bypass the already recorded frozen Bitcoin
identity/domain failures or treat a failed snapshot-generation run as success.
The goal of checking every C jet remains unfinished.
