# Internally linked Bitcoin environment callers

Build these sources only in the isolated `bitcoin` tree prepared by
[`proof-work/linked-repair`](../../linked-repair/README.md).
`C.jets_bitcoin_env` names the original environment AST; `C.jets_sha` names
the same translation unit with the proved reference memcpy linked internally.
The original core AST is linked separately as `C.jets` for shared helpers.

The seven proof-valued aliases instantiate the actual caller proofs with
`memcpy_model_holds`. They are audited with `Print Assumptions` and full types,
not merely counted as definitions. They do not remove SHA startup, readable
raw-memory, tap-path bounds, nonempty-input or other caller prerequisites.
Supplied transaction-id bytes are still copied, not validated or computed.
This is not yet caller-to-original-program or complete runtime composition.

The linker equality uses checked conversion. Whole-program linking alone
inherits CompCert's proof-irrelevance axiom. The normal program's external
libc model, registry, coverage, and assumption policy are untouched. See the
driver's receipts for the program-specific recursive kernel check; no claim
about the external libc implementation follows from this linked variant.
