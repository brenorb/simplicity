# Proof-only count-jet repair for the frozen Bitcoin domain

The complete normal build found a failed conversion in
`C/jet_bitcoin_count_bridge.v`: the original model's `sigTxOutBounds` is
`0 < output_count < 2^32`, but the proof attempted `change` to a proposition
with `0 <= output_count`. These propositions are not convertible.

The one-line repair changes that proof step to the actual strict lower bound.
It changes neither theorem statement, primitive identity, environment domain,
implementation, generation setting nor API. No premise is added. It does not
claim to represent empty-output environments in the frozen model.

## Checked implementation-to-specification results

A separate derivative tree freshly compiles the repaired bridge and the
unchanged `C.jet_bitcoin_count_local` against it. Its existing complete
`bitcoin_num_inputs_local_spec` and `bitcoin_num_outputs_local_spec` endpoints
prove the actual individual C functions against their literal firstFail-based
Simplicity programs over Bitcoin primitives, with the existing physical
environment relation and full source/output/frame/memory contract.

Historical verification receipts remain tied to their original entire input
inventories. Promoting this unrelated proof repair into the checkout does not
retarget old receipts or certify the entire new checkout. Their sealed source
trees and theorem/dependency identities remain unchanged; an old verifier that
requires its earlier whole-checkout fingerprint should reject a later changed
checkout rather than silently blessing it.
