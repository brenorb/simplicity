# Six-module token proof bundle for normal registration

This consolidates the two already checked token-amount endpoints and their
previously unregistered dependencies. It adds no new proof source or coverage,
and does not change a theorem or specification.

All six modules were explicitly rebuilt: local-zero initialization, pointer
selection/armed execution, shared allocation/framing composition, complete
static helper, indexed/current wrappers, and literal specification bridges.
All36 result types and31 definitions were printed in full;13 results are
closed. The four endpoint statements (canonical-Coq and literal, for two actual
C functions) each retain exactly the six inherited Coq/CompCert assumptions.

The source guards are byte-identical copies of those in the completed token
proof folder, not a relaxed correspondence. Normal registration can deploy
that original guard pair under `elements-token-amount-complete/`. The new normal
candidate is tracked in `../elements-token-admission/`; it must audit all six
modules' declarations, types, definitions and assumptions, not just the last
literal endpoint module.

This is not normal full acceptance or installation. Main remains407 while
actual-main407 and isolated415 audits run (37961 and63601); keep their semantic
inputs frozen. Caller/domain, host-library/fidelity, configuration and the104
existing `memcpy_model` conditions remain explicit. The every-jet goal is not
complete. These receipts bind the actual dirty/staged base, not clean HEAD.
