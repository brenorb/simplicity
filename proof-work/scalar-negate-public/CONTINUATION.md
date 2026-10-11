# Next: normal candidate integration, not another scalar-negate caller proof

The all-533-jet goal remains active and incomplete. This turn completed the
original scalar-negate **public local** implementation-to-literal theorem;
it adds no main registered coverage yet. Main registration remains 351/533.

## Completed proof closure

- `../scalar-negate`: 22 checked actual helper/carry/mask/storage results.
- `../scalar-negate-canonical`: 14 checked literal-program/helper bridges.
- This archive: 11 checked actual call-sequence, public lifecycle and final
  local theorem results. Do **not** redo the proof decomposition from the
  older canonical continuation: it is now complete.
- The earlier scalar-normalize complete public local theorem and whole
  serializer are in `../scalar-normalize` and `../scalar-writer`.

Actual current scratch: `/tmp/jet-scalar-negate.f4CRAT` (`NegC`).
Original dependencies: `/tmp/jet-scalar-reverify.8hswEF` (`OriginalC`).
Writer/normalize dependencies: `/tmp/jet-scalar-writer.khT8eN` (`WriterC`).
Accepted C baseline: `/tmp/jet-ge-negate-accept.5mtyZa/Coq`.

All five new modules compiled without failures; the final declaration is
`scalar_negate_local_spec`. Independent kernel session **27657** is terminal,
exit **0**; assumptions session **39820** is terminal, exit **0**. Contract
printing completed directly with exit **0**. No pending proof driver is part
of this result. The inherited public contract definition was printed and
reviewed, not merely the abbreviation in the final theorem type.

Working command from the accepted baseline's `Coq` directory:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqchk -silent -o \
  -R /tmp/jet-scalar-reverify.8hswEF OriginalC \
  -R /tmp/jet-scalar-writer.khT8eN WriterC \
  -R /tmp/jet-scalar-negate.f4CRAT NegC \
  NegC.jet_secp_scalar_negate_writer_identity \
  NegC.jet_secp_scalar_read_negate_write \
  NegC.jet_secp_scalar_negate_rest \
  NegC.jet_secp_scalar_negate_lifecycle \
  NegC.jet_secp_scalar_negate_local
```

## Verified live acceptance: preserve its inputs

Session **45608** owns full scalar-zero normal acceptance in
`/tmp/jet-scalar-zero-accept.smyVL2/Coq`. It was revalidated live this turn.
The log `/tmp/jet-scalar-zero-accept.smyVL2/scalar-zero-full-acceptance.log`
reports kernel checking passed on **804 modules**, followed by the ongoing
assumption gate. Earlier static/canonical/negative gates and normal build
passed. There is no terminal full-acceptance result yet.

Poll that same process. Do not restart it or mutate any input merely because
it is quiet. Pre-acceptance fingerprint:
`c4027e45b7c0b61edc21ee42e2e72a64a79ff4465002033dc18be5bb0cfc8657`.
356/533 is provisional candidate coverage, not accepted main coverage.
On terminal exit zero, review complete final log, exact dependency/contracts
gates, four AST matches and unchanged ending fingerprint before an acceptance
receipt. On failure inspect the first actual diagnostic before modifying it.

## Next actions

1. Review scalar-zero full acceptance when it terminates, preserving its
   frozen candidate. Do not edit main mixed dirty registries in the meantime.
2. Assemble a **separate** namespace-C candidate over the accepted scalar-zero
   baseline, adding scalar-normalize and scalar-negate and their actual
   dependency closure. From the archived module texts, recursively resolve
   `WriterC.` and `NegC.` imports, replacing them only with `C.`; verify all
   `OriginalC.` dependencies match the new baseline's already checked scalar
   modules. Existing aliases resolve to C and must not overwrite real modules.
3. Roots are `jet_secp_scalar_normalize_local`,
   `jet_secp_scalar_negate_local` and corresponding parametricity modules.
   The owned-getter scratch modules are **not** dependencies of the complete
   writer; do not copy unrelated experiments. Actual writer getter calls
   already use the original `secp_pure` verified function table.
4. Extend only the new candidate's project inventories, public results,
   contract definitions, coverage validation and literal/public gates for
   the two new jets. Candidate coverage would become 358/533 if both are
   successfully accepted over the 356 baseline; that is not current coverage.
5. Fresh-compile all namespace-transported sources. Generate and review
   normal types/definitions and exact per-result dependencies against these
   checked archived results. Keep inherited snapshots unchanged except for
   reviewed additions; do not mistake generation for acceptance.
6. Run full `check-jets.sh --accept` without update/no-build shortcuts and
   preserve the actual session, exit status, immutable input fingerprint
   and logs. Register/reconcile the main checkout only after success,
   preserving unrelated staged/unstaged and SHA work.
7. Then continue easiest remaining scalar/other jets, reusing actual reader,
   serializer and lifecycle contracts while proving each new arithmetic
   implementation and its own literal specification. The all-jet goal also
   retains shared/evaluator-domain and build-configuration obligations.

## Coordination and scope

Claude owns shared memcpy linkage, SHA startup, frame/Bit-Machine premise
constructibility and the Elements translation-unit/getter foundation. Those
are disjoint from this secp scalar work; their files/worktree are untouched.
No install, production C/Haskell change, new premise, admission or push.
These results remain local-frame / LP64 / RECKLESS, not arbitrary evaluator
frames or assertion-enabled builds.
