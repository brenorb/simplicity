# Ordinary-module integration of the complete beta jet

The normal project endpoint is
`C.jet_secp_beta_local.fe_multiply_beta_initialized_local_spec`. It retains
the complete existing initialized frame/memory contract for unrestricted
Word256 inputs and the literal pinned Simplicity specification. The beta global
is initialized by the real program and its invariant is preserved. No new input
separation condition, numerical range premise, helper-execution premise or
external-library model is introduced.

This is an **unregistered integration candidate**, not shared acceptance or a
claim that the every-jet goal is complete. The pending main registry, projects,
snapshots and unrelated staged patch are not edited. Accepted-coverage delta: zero.

## Exact reconstruction, not proof substitution

`assemble.py prepare` materializes 230 inherited modules and nineteen extensions
from committed checked sources at `f03579af`. Ordinary inherited field modules
that existed only in the earlier isolated integration are reconstructed using
their committed historical source manifest and its exact reversible mapping.
No uncommitted original or prebuilt object is used as a proof source.

The new nineteen-module mapping changes only qualified module-name tokens and
is checked in both directions. Unqualified definitions, theorem statements,
tactics, C code, specification values and generation settings are unchanged.
The reusable borrowed-region and internal-Clight preservation modules receive
generic `C.*` names; beta-specific adapters receive `C.jet_secp_beta_*` names.

The candidate is `/private/tmp/jet-beta-integration-qctc10_1`. Its existing normal
project contents are retained, with missing source membership appended. A new
`coq_makefile`/`make` dependency build compiles the ordinary endpoint and all
249 modules in its actual closure from source, using the pinned Coq 8.17.1,
CompCert and VST paths. There are no private namespace flags or copied `.vo`s.
This focused target is not a build of every unrelated registered jet.

The driver logs include expected unsuccessful Git lookups for archive-only
ordinary source paths. Those sources are then recovered from committed proof
archives and checked against the original source hash. These lookup diagnostics
are not failed Coq proofs; `beta-normal-build.log` and the terminal command
status record the actual successful compiler run separately.

## Verification phases

```sh
python3 -B proof-work/secp-beta-integration/assemble.py prepare
python3 -B proof-work/secp-beta-integration/assemble.py build
python3 -B proof-work/secp-beta-integration/verify.py reports
python3 -B proof-work/secp-beta-integration/verify.py kernel
python3 -B proof-work/secp-beta-integration/verify.py check
```

Mutating phases are one-shot: poll their original process handles. Launch files
are not completion receipts. `PREPARATION.json`, `BUILT.json`, `REPORTED.json`
and `CHECKED.json` distinguish exact reconstruction, completed fresh normal
build, completed reports/review, and completed recursive kernel verification.
The final command is read-only and validates the exact checked identities.

The full reports cover all 107 extension result types and 32 definitions.
Every type and definition is compared to the original full report after resolving
only known module-name/printing aliases and whitespace. Assumptions are compared
result-by-result to their exact original profiles: 68 closed, sixteen with the
four inherited classical/extensionality assumptions, two with dependent
functional extensionality alone, and 21 with the original six Coq/CompCert
assumptions. The public endpoint retains exactly those six; the two generic
external-properties assumptions are not added.

The actual loaded local-library inventory must equal the 249 source-built
modules, with no private proof namespace. The original-target guard independently
checks all 240 frozen C, canonical Haskell and generation-configuration inputs.
The actual ordinary public contract also passes the six mutation fixtures for
wrong input/output width, wrong C function, arbitrary readiness, replacement
specification and an added premise. The literal/global source port is the exact
reversible rename of the already checked one, not a newly simplified term.

## Next: registration and full acceptance

Prepare a **different** registration candidate. Preserve all existing entries,
including the reviewed field-multiplication addition; combine the exact ordinary
source closures rather than overwriting either historical checked tree. Add the
strict `FeMultiplyBeta` coverage contract, literal/source gate, mutation tests,
audited theorem/definition entries and normal project membership. Keep the
named `beta_initialized` predicate and its full definition audited; do not
accept arbitrary readiness or a helper offered as the public result.

Generate snapshots only in that candidate, review the complete contract and
assumption diffs, then attempt normal `check-jets.sh --accept` without update or
no-build shortcuts. The earlier full attempt in `../secp-field-acceptance`
failed the frozen Bitcoin primitive-identity gate; the frozen value-domain
failure also remains unresolved. Those historical failures are not a successful
run on this new candidate. Do not bypass them, change original targets or erase
evidence to obtain acceptance; continue independent proof work where possible.

The proof-only Bitcoin count repair is already committed in the main branch.
Any acceptance candidate reconstructed from an older base must preserve that
proved repair without changing its public domain or conclusions. Main checkout
promotion remains separate from isolated proof/integration success.
