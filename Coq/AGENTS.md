# Jet proof integrity

Preserve the public theorem and canonical specification being proved. Do not
replace a required execution, output or framing fact with an assumed premise.
Explicit external-library models are conditional results and must remain
identified as such in coverage and documentation.

Do not use `admit`, `Admitted`, assumed declarations or disabled kernel checks,
including in temporary proof experiments. Inspect goals with `Show` in an
interactive session or stop an incomplete scratch file without compiling it.
Keep scratch sources outside the repository and out of the build load paths.

Snapshot generation is not acceptance. Review the type, definition and axiom
diffs before running `check-jets.sh --accept` without update flags. Do not edit
proof sources, manifests, C inputs or canonical specifications during a running
audit. Preserve its exit status and log; a stale `.vo` is not verification of
the current `.v`.

The canonical Bitcoin primitive namespace is `Bitcoin`; an extended Coq module
does not create a new primitive namespace. Run the identity gate when changing
the primitive interface. It checks identity, not the cryptographic correctness
of cached hash values or their environment projection.
