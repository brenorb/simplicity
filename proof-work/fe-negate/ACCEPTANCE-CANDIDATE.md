# Literal field-negation acceptance candidate

Candidate root: `/tmp/jet-negate-accept.ftWsqQ`. This is isolated from the
checkout's completed range acceptance (24458, exit 0). No accepted coverage is added
by this record, and neither audit should be restarted on an observation timeout.

The base is the independently accepted reconciled range tree at
`/tmp/jet-range-consumer.RbIhbg/Coq`, fingerprint
`dccfcbcd42e6b7c419992597362ebf4a2c2df407769183a217a27599718e8f07`.
The production C/Haskell directories are linked read-only by convention to the
unchanged repository target. Do not edit them during verification.

## Completed candidate assembly and checks

- All 32 archived sources/review files were extracted with `manage.py` into
  `ports/`. The 23 proof modules were materialized under `Coq/C/`; the four
  source gates, four mutation suites and reference JSON under `Coq/negate-review/`.
- Both Coq project inventories include all 23 modules. All 87 named proof
  results are in the public assumption/type inventory; 35 supporting definitions
  are in the definition inventory.
- Only `C.jet_secp_negate_literal_contract.fe_negate_literal_local_spec` is
  registered as final jet coverage. The older optimized-port theorem remains
  audited support, not the registration. Candidate coverage is provisionally
  350/533; actual-checkout coverage remains 349/533.
- The four source gates pass; 19+86+15+32 = 152 targeted mutations are rejected.
  Coverage metadata tests additionally reject wrong functions/contracts and an
  impossible premise for the new registration.
- Fresh whole candidate build completed with exit 0 (85382), log `build.log`.
  No admissions, unsafe flags, production changes or extra external models were
  introduced. The archive's earlier independent kernel receipts still do not
  replace the pending candidate-wide acceptance.

`acceptance-infrastructure.patch` preserves the project/audit/coverage/gate
edits relative to the accepted range base. Apply it only after materializing
the archived proof sources and gates at the paths above; it includes the
review-reference SHA-256 pin. That pin makes changes to the JSON fail a
fingerprinted checker rather than silently alter the reviewed baseline.

## Live work and remaining steps

Snapshot generation completed with exit 0 (27347), and actual snapshot review
is recorded in `SNAPSHOT-REVIEW.md`: all old records preserved verbatim, 87 new
results, 35 new definitions, unchanged kernel allowlist. Logs:
`assumptions-update.log` and `contracts-update.log` in the candidate root.

The trailing blank line of `Coq/C/jet_secp_negate_local.v` is now restored and
the dependent chain rebuilt successfully (77960). All 23 proof sources match
the archive byte-for-byte.

There are no changes to old types, definitions or assumption records and no
printer-qualification exceptions. The archive manifest's eleven previously
omitted division lemma names are corrected without changing proof sources.

Separate frozen `check-jets.sh --accept` **57174 passes with exit 0**, without
snapshot-update flags, log `/tmp/jet-negate-accept.ftWsqQ/accept.log`, SHA-256
`367e6e59bd7d9d1805894a647c22c4c6214c89c81bb1cbcde02cbe6137b33427`.
All 626 kernel modules, assumption/contract/negative gates, four original-source
AST comparisons and the final fingerprint check pass. This is a full isolated
candidate receipt, not yet an actual-checkout receipt.

All 42 reviewed files are now guarded-integrated. `INTEGRATION-GUARDS.json`
records exact old/new hashes; only the recursive gate's reviewed JSON-hash pin
differs from its archived checker. The 23 proof files match their archives.
Old 3583 assumption records and old printed contracts are unchanged. Integrated
checkout pre-run SHA-256:
`f87884d8fcd444670dcd1824e0cd616b2c78fac29bae7da90d2ebfe158724c85`.
Actual-checkout `check-jets.sh --accept` runs as **57052**, log
`/tmp/jet-negate-integrated-accept-2026-10-09.log`, without update flags,
Coq 8.17.1, 65520 KiB stack and two build jobs. Poll that exact handle, do not
restart it on yield, and keep its Coq/C/Haskell inputs frozen to terminal status.
The registry is provisional 350/533; obtain actual checkout acceptance before
counting this as accepted checkout coverage. Existing shared-domain/evaluator and
inherited exhaustive fidelity review obligations remain open.

No new commit is claimed here. The configured signing agent previously refused
the operation; unsigned commits or disabling signing have not been authorized.
Nothing is pushed by this continuation.
