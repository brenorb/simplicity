# Isolated normal447 preparation: four Elements C-to-program endpoints

The proposed additions are the original C `input_annexes_hash`, `tapleaf_hash`,
`tap_env_hash` and `input_outpoints_hash` against their actual primitive
programs. They reuse the environment-generic SHA element loop, literal tag
semantics, verified component programs and whole-function C getter proofs.
All four proof packages already passed fresh compilation/reporting, recursive
kernel/Elements-AST checks, canonical-source and independent evidence reviews.
Their exact source is reused; no inherited proof is overwritten.

Assembly and preparation completed with exit zero:

Coverage requires the entire reviewed C-to-program theorem for each function,
including its actual C function, global/logical environments, types, cache/frame
relation and exact program interpretation. A generic cache helper, wrong
function/environment or weakened/vacuous premise cannot count. The twelve
runtime source guard/model files participate in the normal audit fingerprint.

`normal-delta-review-v6.py` preserves every other v5 check and adds an exact
completed-proof source mapping, since these modules belong to multiple completed
proof trees. Missing/extra source keys, symlinks and a self-referential candidate
as its own proof source are rejected. Historical v5 code/receipts stay unchanged.
The earlier single-proof-tree interface failure was an audit-tool limitation,
not a C/specification mismatch or a reason to bypass source comparison.

The candidate proposes447/533 entries:343 without an extra library premise,
104 still conditional on `memcpy_model`, with86 declarations unregistered.
Caller cache construction, host-library and other previously documented
boundaries remain explicit. Full447 acceptance, main installation, discharge
of those remaining obligations and completion of every jet are not claimed.
