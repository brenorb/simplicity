# Null-data jet: overlapping input/output storage

## Result and boundary

`C.jet_elements_null_overlap_counterexample.null_data_overlap_counterexample`
proves a successful execution of the **original public Clight jet** on original
input `(0,0)` whose output disagrees with `Elements.sem OutputNullDatum`.
The initial memory and logical environment are constructed, not assumed to
exist. The theorem establishes the existing null-data environment relation,
the encoded input, writable output, actual call, success and final cursor zero.
There is no execution, allocation, output-value or libc-model premise.

**This is a represented-memory overlap counterexample, not a formal proof of
real-builder or evaluator reachability.** The constructed opcode cache points
into otherwise unread bytes of its output structure, including offset +32.
It satisfies the existing null-data projection, not a whole-transaction
representation or the allocation layout of `env.c`. The earlier native tests
use the actual transaction/taproot/environment builders; that is independent
evidence, not a formal connection to this constructed memory.

Input/output backing storage overlaps. Environment storage is separated from
the destination frame field and output bytes. The accepted BitMachine theorem
requires evaluator-valid separated frames and is **not refuted**. This
diagnostic adds no coverage and does not alter any API contract.

## Expected versus actual

| Observation | Frozen primitive | Original C execution |
| --- | --- | --- |
| Original indices | `(0,0)` | `(0,0)` |
| Selected script | `6a 51` (`OP_RETURN OP_1`) | Represented one-datum OP_1 cache |
| Result tags | `1,1`: output and datum present | `1,0`: output present, datum absent |
| Return / final destination cursor | Not an execution observation | Success / zero |

The order in `C/elements/elementsJets.c:425–429` is: read `i`, write the outer
tag, read `j`. In the 64-bit layout, the output cursor is initially 261,
the write edge is zero, and the read edge is 40 bytes. The first output tag
sets bit 4 of the shared word at byte offset 32. This changes the unread
second index from zero to 16. The one-datum bounds check therefore returns
"datum absent". `overlap_original_spec_value` checks the original primitive's
present/present OP_1 result; the final theorem contradicts its encoded second
tag using the actual post-call memory.

## Is it a bug, and was it introduced by these proofs?

It is a wrong-result discrepancy on overlapping stand-alone calls. If
individually valid frames are meant to suffice for that API, it is a bug in
that broader domain. The meaning of API frame validity must not be silently
changed to settle that design question. No such change is made here.

The read/write/read order is already present at upstream base `91d89bac`;
`C/elements/elementsJets.c` is unchanged from that revision at proof baseline
`9bc10108`. This work changes neither production C nor the specification,
generated program, generation settings or API documentation.

## Verification and reproduction

The normal modules separate exact stores/read effects and the complete public
call (`jet_elements_null_overlap_exec.v`), memory construction
(`jet_elements_null_overlap_env.v`), and the valid logical environment,
representation and final mismatch (`jet_elements_null_overlap_counterexample.v`).
They compile with the project's Coq 8.17.1 baseline and pass recursive kernel
checking. The final theorem retains the six inherited assumptions, without an
additional external-library model. No proof is admitted or skipped. Public
types, relevant definitions and assumption sets use the existing snapshot
audits; no new checker or gate exemption is introduced.

With the baseline toolchain and prepared dependencies:

```sh
JET_TARGETS=C/jet_elements_null_overlap_counterexample.vo bash Coq/build-jets.sh -j2
ulimit -S -s 65520
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_null_overlap_counterexample
```

The historical native fixture and specification-only checks remain in
`proof-work/null-data-overlap-validation/`. Its eight sanitizer configurations
and sixteen disjoint controls are native observations, not the new Clight
proof. Its earlier "Clight counterexample remains unproved" text describes the
state at that earlier validation, not the new result above.

## Impact and worst case

The demonstrated consequence is a silent incorrect lookup result despite
success and complete output consumption. An external caller that permits
overlap could make a later decision using an absent datum instead of OP_1;
which higher-level decisions are affected depends on that caller. No such
caller exploit, consensus failure or evaluator-reachable mismatch is proved.
Neither memory corruption nor a sanitizer error was demonstrated. The native
sanitizer runs do not prove universal absence of undefined behavior.

No repair is applied. Keep the existing separated-frame equivalence and this
broader diagnostic distinct; any production/API/specification correction
requires separate explicit approval.
