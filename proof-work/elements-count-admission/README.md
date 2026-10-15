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

The proposed count is **366/533**, including the unchanged 104 explicit
`memcpy_model` conditions. Main remains **364/533** until reviewed installation.
Neither number completes the all-jet goal or the inherited fidelity review.
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
