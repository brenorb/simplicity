# Jet proof integrity

## Task scope

These rules apply when the current task is formal verification: developing,
debugging, reviewing or auditing Coq/Rocq proofs of an existing implementation
against an existing specification. They also apply when that verification task
would require edits outside this directory.

During such a task, treat the implementation, generated ASTs and canonical
specifications (including `Coq/Simplicity`) as read-only verification targets.
Proof scripts, auxiliary lemmas, faithful proof adapters and mismatch reports
may be edited, but must not change the target's behavior, specification or
required theorem assumptions to make a proof pass.

This is a task-specific boundary, not a repository-wide code freeze. It does
not prohibit implementation or specification changes in a task explicitly
requesting development, improvement or a mismatch fix, even if that task also
updates proofs. Reading this file or working near proof files does not by
itself make a task formal verification. A verification failure alone is not
authorization to switch to fixing the implementation or specification.

## Verification workflow

Before starting proof work and before committing, run
`python3 Coq/check-jet-source-target.py` from the repository root. If it fails,
preserve the frozen targets and report the drift; continue independent proof
work where possible. Do not update the manifest, its hash pins, checker policy,
or CI enforcement to make verification pass. Changing the frozen target or its
acceptance policy requires separate explicit user approval. Proof acceptance
also requires the existing full verification checks.

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

Mismatches between upstream sources (production C, canonical Haskell, the
frozen `Coq/Simplicity` model, or between any two of them) are evidence of
possible upstream bugs for the Simplicity developers to evaluate. Record them
in an existing relevant `Coq/C/JET_*_MISMATCHES.md` report, or create one for
the affected family (paths are relative to the repository root). Include the
exact source locations and revision, expected versus actual behavior, a
reproducible command or witness, and the effect on the theorem and proof
coverage. Distinguish suspected mismatches from those established by closed
evidence; do not present an unproved observation as a verified result.

During formal verification, report mismatches instead of correcting the
verification targets on the spot. Leave the affected obligation explicitly
unproved or conditional, and continue unaffected proof work. Fixing a target
requires a separate explicit development request as described above. Never
relax a gate to hide a mismatch. Gates fail on any
mismatch that is not documented in a report. A documented mismatch is listed
exactly and printed on every run, and it does not block unrelated work.

Evidence is the commit plus one reproducible command (`bash Coq/check-jets.sh
--accept`, or a scoped equivalent). Do not commit logs, receipts or run records
(`*.log`, `RUN.json`, `CHECKED.json` and similar). Write run output to a
temporary directory outside the repository. Anyone can regenerate it by
rerunning the command on the commit.

Before starting a jet proof, check `C/JET_CLAIMS.md` and add a claim line. If
the jet is already claimed, coordinate instead of starting a parallel proof.
Remove your line when the jet is registered or the work is abandoned.
