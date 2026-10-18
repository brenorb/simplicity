# Pinned field-negation dependency (not this branch's work)

The committed field-add modules at the starting commit, and this branch's
writer/canonical-program steps, import the unaccepted field-negation candidate
of the main checkout (`proof-work/fe-negate/`, uncommitted there on
2026-10-18). These files are byte-identical copies of that archive, which is
in turn identical to the live untracked `Coq/C/*.v` files of the main checkout;
`fe-negate-manifest.json` is its manifest (all 23 `.v.source` SHA-256 values
match). They are materialized only into isolated build trees by `../verify.sh`
and are never written into `Coq/C` of a committed tree.

Integration: once the main agent integrates the field-negation candidate, the
`jet_parallel_fe_mul_*` modules compile against the integrated files unchanged
(same module names, same content hashes).
