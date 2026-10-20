# Three original C amount jets against literal specification programs

Complete local C-to-literal-specification contracts now compile and pass
recursive kernel checking for `input_amount`, `output_amount` and
`current_amount`. They reuse the checked actual C executions and preserve each
original representation/frame contract. They are not yet normally registered.

## Specification distinction and shared lemmas

The **primitive** InputAmount/OutputAmount returns only a confidential Word64.
The **jet** specification is the canonical Transaction program pairing that
primitive with InputAsset/OutputAsset. Its `ih &&& oh` routing produces
**asset then amount**, the order written by the C jet. CurrentAmount is
CurrentIndex followed by the assertion of the inputAmount program. The source
guard binds those actual programs and the corresponding Coq combinator body;
it does not replace the jet specification with the simpler amount primitive.

The asset family's payload-polymorphic confidential encoder is reused at
Word64. Explicit values use the existing low-bit-first word conversion applied
to the unsigned 64-bit value. Confidential values reuse the packed-field-word
projection. The new generic `amount_pair_literal_matches` then reuses the
payload-polymorphic indexed bridge. No field arithmetic, extra successful
execution premise or desired-output hypothesis is introduced.

The concrete C contracts include entry/source copying, actual reads,
count/index decisions, asset/amount helpers, writes/skips, return/free, arbitrary
initial output contents, prefix/cursor and memory framing. The explicit amount
branch's 193 padding cells, confidential 256-bit payload, and 516-cell pair
span are retained, not zero-initialized or shortened. Initial represented
arrays, bounded pointers, footprints and the logical valid-current-index
condition remain the original ones. Caller construction and the inherited
empty-array/null-pointer boundary are not discharged here. LP64/RECKLESS and
host-library/fidelity boundaries remain explicit.

## Completed verification

The new module has eight results and five definitions. The encoder and generic
pair bridges are closed. Three specification transports retain functional
extensionality; each concrete C endpoint has exactly the six inherited
assumptions, without a new libc model.

An initial definition needed its payload type supplied explicitly because
`tySem` is non-injective. Giving `X`, `AmountPair` and depth 5 resolved that
inference mismatch without changing the theorem. The complete corrected module
compiled. Checker 32972 then freshly compiled the original
`C.jet_elements_amount_jets` and `C.jet_elements_current_gen_jets` execution
modules before `C.jet_elements_amount_literal`, printed all thirteen full new
type/definition records and actual assumptions, regenerated the Elements AST
and recursively kernel-checked the full dependency closure. Exit status: 0.
No admissions, assumed declarations or unchecked casts are used.

Normal registration and full acceptance remain separate. Prepare an isolated
successor over the reviewed asset410 source candidate; do not edit the live
combined407 candidate. Main stays401, with the original staged patch preserved.
Audits 92989 (main401), 26900 (isolated402) and 23810 (combined407) continue on
their existing frozen source trees. The full every-jet goal, including the
104 explicit `memcpy_model` conditions, remains unfinished.
