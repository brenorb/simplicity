# Checked secp conversions and frame constructibility

Four preexisting conversion proofs in the accepted secp dependency tree used
unchecked casts. This phase replaces **only** those four proof sentences with
`timeout 10 (vm_compute; reflexivity)`, retaining all statements, definitions,
other proofs and production C:

- `jet_secp_fns.secp_pure_lookup`;
- `jet_secp_fe_nv.nv_run_eq`;
- `jet_secp_fe_b32.sb_run_eq` and `gb_run_eq`.

All four checked equalities compile and are closed under the global context.
The previous source scanner did not reject either unchecked-cast tactic. Its
normal rule now rejects both `vm_cast_no_check` and `native_cast_no_check`;
the normal gate's negative fixtures retain tests for both. The diagnostic
strings are never sent to Coq or compiled as candidate proofs.

## Completed checks

The external candidate `/private/tmp/jet-secp-checked.rxj2k4b8` contains 138
C/support modules. Sixty-nine unaffected objects were reused only after exact
source/object comparison with the completed count audit; all repaired/new
modules and the remaining dependencies were freshly built. Independent
recursive `coqchk -o` checks the entire selected closure, including the actual
normalization, odd and zero public local contracts. It does not certify every
other secp consumer or replace whole-registry acceptance.

Twenty exported results have complete, untruncated type/assumption reports;
fourteen are closed and the other six stay within the six inherited execution
assumptions. The fifteen-axiom library context is unchanged; type-in-type,
unsafe fixpoints and assumed positivity categories are all empty. The original
production secp AST regenerates byte-for-byte. Eighteen proof/evidence
corruptions and twelve proof-escape examples are rejected. Checked computation,
comments and strings remain accepted. Eleven further corruption fixtures
check the explicit existing-source preservation overlay.

`ASSEMBLY.json`, `REVIEW.json` and `EXTRA_REVIEW.json` bind source and object
hashes, exact commands, terminal logs, original C generation and full printing.
`source/` preserves the checked new/repaired sources. No compiled objects are
installed into main and no public proposition is weakened.

## Imported caller result

The previously excluded `jet_frame_constructible_secp.v` is now installed
source-only from frozen Claude commit
`30404face45383153528f36d915de6d7df11f3f4`, byte-for-byte. With the repaired
dependencies it compiles and recursively kernel-checks unchanged.

For every input and every preexisting memory, its three concrete results
construct valid fresh frames for field normalization, odd and zero, execute
the actual original-C functions under `secp_ge`, return one, write encoded
specification results, and preserve preexisting loads. The generic theorem
takes the corresponding local contract and frame-size bounds. The concrete
instances discharge those premises from the existing local proofs and actual
widths. It does not generalize the original local contract's frame domain or
prove dispatch/evaluator composition.

## Installation and preservation

`INSTALLATION.json` records five intentional existing-source changes (three
proof files plus the scanner and its normal regression-test file), one new
module and the exact original index hash. The old integration baselines remain
immutable. Their preservation checks now compose the precise before/after
repair overlay in `preservation.py`, in addition to their existing additive
source ledgers. This overlay reconstructs only the four proof replacements and
the exact scanner/fixture strengthening from commit `87e9ad7b`; it rejects
other source edits or mismatched baseline hashes. It is not an allowlist for
arbitrary changes or axioms.

The linked audit also pins its own historical driver. Its old receipt remains
unchanged: provenance validation accepts that recorded hash only when Git's
original driver is reconstructed with the **exact** preservation-hook and
provenance-hook additions. Unknown edits, missing checks and unknown receipt
hashes are rejected. The pre-follow-up policy source is retained under
`historical-tools/`, matching the original supplemental audit's tool hash;
this bookkeeping follow-up does not replace any Coq/kernel evidence.
The linked audit's existing sixteen corruption tests and six lexical fixtures
also pass against that successor, including rejection of a changed driver hash.

Coverage remains **364/533**. No registry, manifest, contract snapshot, canonical
specification or production C changes. This is a source-policy repair and
non-vacuity result, not new admitted jet coverage or full-checkout acceptance.
The existing staged and unrelated unstaged/untracked work is preserved.

Post-installation checks:

```sh
python3 -B proof-work/secp-checked-conversions/review.py validate /private/tmp/jet-secp-checked.rxj2k4b8
python3 -B proof-work/secp-checked-conversions/test-review.py /private/tmp/jet-secp-checked.rxj2k4b8
python3 -B proof-work/secp-checked-conversions/test-preservation.py
python3 -B proof-work/linked-repair/run.py post-check
python3 -B proof-work/claude-remainder-integration/run.py post-check
(cd Coq && python3 -B scan-jet-proofs.py)
```

The `prepare/check/finish/install` commands are the recorded pre-installation
workflow, not a way to overwrite the now-repaired main sources. `install.py`
refuses a second application. Subsequent full builds must compile these current
checked sources and their consumers, not copy old main `.vo` files over them.
The next admission batch is the two Elements count jets, with their literal
program/observation review and any-payload C contracts already checked. Prepare
and review registry/snapshot additions in a separate copied tree, rebuild all
registered chains under the strengthened scanner, and obtain full acceptance
without update/no-build flags before installing/counting that metadata.
