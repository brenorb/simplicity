# Elements count jets: normal admission candidate

This batch registers only `simplicity_num_inputs` and `simplicity_num_outputs`,
against the unrestricted original-C local contracts in
`C.jet_elements_count_local`. Their targets remain the literal canonical
`firstFail word32` programs, not a replacement count primitive or an assumed C
execution. The full execution, output, prefix, cursor and memory guarantees
are unchanged.

Four modules are added to both manifests, with eighteen public results and six
contract definitions: canonical programs, list-search bridges, actual-C local
contracts and the any-payload contracts. The any-payload results formally show
that count does not depend on the indexed hash values. The separate checked
frame/environment constructibility proofs remain available without importing
unrelated Elements candidate jets into this normal registration batch. No
existing proof source is edited.

The normal checker gains the selected source guard and its 49 negative fixtures
(plus the deliberately accepted observation-only payload mutation). Coverage
bookkeeping allows only the two additional reviewed names; twelve new cases
reject wrong functions, linked/logical environments, widths, contract shapes
and vacuous premises. A separate sixteen-fixture review checks the exact
registration, inherited snapshots, sources and command/exit evidence.

## Status and scope

Preparation/review is committed and pushed as `2f69bf90`. The whole normal
build and all four explicit fresh compiles passed. Review retained all 7,374
inherited contract records byte-for-byte/in order and all 4,878 inherited
dependency records. All twenty-four new deep records passed; two compact
records needed checked deep supplements. Source, coverage and sixteen evidence
corruption fixtures passed.

The full isolated acceptance run (session **96437**) terminated with exit 0
after 3,126.87 seconds. Static/source checks, the normal build, recursive
`coqchk` on all 960 registered modules, per-result assumptions, full contract
snapshots, negative tests and all five production AST regenerations passed.
`ACCEPTANCE.json` and `TERMINAL.json` bind its actual terminal output and
unchanged input fingerprint. A durable identical log is `acceptance.log`.

The exact reviewed metadata/gate delta was then installed in main, without
changing any proof/C/Haskell source or compiler object. `INSTALLATION.json`
and `DELTA.patch` bind that installation. The complete old source map plus
this exact delta equals the actual main map, and the preexisting staged patch
is unchanged. The main source fingerprint now exactly equals the accepted
candidate's `aa2c41604a5cae0c69d6900799ecd8b6a824b26ec3c4b2b4bcf23cb6817f5bce`.

The separate actual-main acceptance (session **49451**) also terminated with
exit 0 after 3,474.96 seconds. `MAIN-ACCEPTANCE.json` binds the unchanged
`aa2c4160...` input fingerprint and complete successful log; its durable copy
is `main-acceptance.log`. Build, all 960 kernel-checked modules, assumptions,
contract snapshots, negative tests and all five production ASTs passed in the
actual checkout. `post-check.py` confirms both exact accepted-source identity
and unchanged preexisting staging, with `actual_main_acceptance: true`.
`MAIN-AUDIT-RUN.json` and the installation ledger keep their historical launch/
installation meanings; neither was rewritten to masquerade as a terminal run.
Do not restart either completed count acceptance.

The isolated tree is `/private/tmp/jet-count-admission.ww8e4z3b`. `ASSEMBLY.json`
pins the complete main source map, staged patch, exact additions and cached
objects. Preparation rebuilds the normal project and explicitly recompiles
all four count modules. Only source-identical, hash-bound objects from earlier
completed audits are imported; no compiler-output symlinks into main are used.

Preparation is **not acceptance**. A valid `REVIEW.json` must establish that
all inherited contract records remain byte-identical/in order, inherited axiom
sets are unchanged, the eighteen new dependency sets stay within the six
inherited assumptions, and all twenty-four new type/definition records agree
with untruncated output. An elided compact record is checked against its full
counterpart, never omitted. Each fresh compiler command and object is bound.

Only a terminal `ACCEPTANCE.json` with exit 0, the unchanged input fingerprint
and the complete final marker establishes isolated full acceptance.
`AUDIT-RUN.json` records launch, not success. The gate is exactly
`bash check-jets.sh --accept`, without update/no-build/unsafe flags: all
registered modules, kernel chains, assumptions, contract snapshots, negative
tests, source targets and all five production ASTs must pass.

Installed main registration and the fully accepted isolated candidate are
**366/533**, including the unchanged 104 explicit `memcpy_model` conditions;
both isolated and actual-main full acceptance have passed. This does not
complete the all-jet goal or the inherited fidelity review.
The count domain remains bounded by the C raw uint32 count interface, not
arbitrarily large Haskell vectors. Full Elements environment-builder and
runtime/evaluator composition remain distinct obligations.

## Workflow

```sh
python3 -B proof-work/elements-count-admission/admission.py assemble
ulimit -s 65520
python3 -B proof-work/elements-count-admission/admission.py prepare /absolute/candidate
python3 -B proof-work/elements-count-admission/review.py finish /absolute/candidate
python3 -B proof-work/elements-count-admission/accept.py /absolute/candidate
```

Keep candidate Coq sources, C/Haskell inputs, registries and snapshots frozen
during the full audit. Poll its existing live process, not a replacement run.
The optional `seal` command pins objects from the initial in-flight preparer
that predated the added hash fields; it preserves its original terminal
receipt and does not rerun or reclassify a check.

After terminal isolated acceptance, `install.py /absolute/candidate` may install
only the exact seven metadata/snapshot files, three gate scripts and two guard
files. It first rechecks the complete old main source map and index. Its delta
is archived separately as `DELTA.patch`; this avoids committing unrelated dirty
metadata or changing the user's staging. No proof/C/Haskell source or `.vo` is
installed. Main's resulting full source fingerprint must equal the accepted
candidate's exactly. Actual-main acceptance remains a separate terminal run.
`INSTALLATION.json`, if present, records installation rather than claiming that
separate main run already succeeded. The all-jet goal stays active.

Guarded post-acceptance workflow (installation and main launch already done):

```sh
python3 -B proof-work/elements-count-admission/install.py /absolute/candidate
python3 -B proof-work/elements-count-admission/main-accept.py
python3 -B proof-work/elements-count-admission/post-check.py
```

The installed-main precheck and full compiler/checker run both passed with
exact source identity and staging preservation. After a later reviewed batch
changes main's source fingerprint, this count ledger remains historical
evidence: do not run its unchanged-source postcheck as if the checkout still
contained only this delta. The next admission needs its own composed ledger.
