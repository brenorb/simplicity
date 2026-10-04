# Jet proof integrity

Follow the proof-integrity rules in [AGENTS.md](AGENTS.md), including for scratch
experiments: no admits, assumed declarations or disabled kernel checks. Inspect
unfinished goals without compiling a placeholder proof.

Preserve canonical specifications and public postconditions. Report
`memcpy_model` results as conditional; the extended Bitcoin interface still uses
the canonical `Bitcoin` primitive namespace.

Review generated snapshot diffs, then validate the final sources with
`bash Coq/check-jets.sh --accept` from the repository root. Snapshot update mode
is not acceptance. Do not edit audit inputs during verification, and check the
actual exit status rather than a pipeline's last command or a stale `.vo`.
