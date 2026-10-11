# Next: complete the public scalar-negate caller

**Superseded proof work:** the public caller is now fully compiled and
independently kernel-checked in `../scalar-negate-public`. Its continuation
guide records the next integration work. The decomposition below is retained
as historical guidance, not as unfinished proof work.

The app goal remains active and incomplete. This checkpoint adds no main
coverage. The main registered total is still 351/533; isolated candidates
must not be substituted for it. No remote push is authorized.

## Verified starting point

- `../scalar-negate`: five modules / 22 checked original in-place C helper,
  carry, mask, concrete-storage and serializer-ownership results.
- This archive: three modules / 14 checked literal multiply/mod512 scalar
  bridges, parametricity and actual helper-to-canonical-storage contract.
- `../scalar-normalize`: a checked complete public local normalize theorem,
  and `../scalar-writer`: a checked complete original serializer.
- Sources are materialized under `/tmp/jet-scalar-negate.f4CRAT` (`NegC`).
  Original scalar dependencies are `/tmp/jet-scalar-reverify.8hswEF`
  (`OriginalC`); serializer/normalize dependencies are
  `/tmp/jet-scalar-writer.khT8eN` (`WriterC`). Accepted `C` baseline:
  `/tmp/jet-ge-negate-accept.5mtyZa/Coq`.

Working command from that baseline's `Coq` directory:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
bash build-jets.sh --coqc \
  -R /tmp/jet-scalar-reverify.8hswEF OriginalC \
  -R /tmp/jet-scalar-writer.khT8eN WriterC \
  -R /tmp/jet-scalar-negate.f4CRAT NegC \
  /tmp/jet-scalar-negate.f4CRAT/NEXT_MODULE.v
```

## Proof decomposition

1. Prove normalization after literal scalar-negate is identity using
   `toZ_injective`, `canonical_scalar_normalize_numeric`,
   `canonical_scalar_negate_numeric` and the positive group-order bound.
   This permits reuse of the existing serializer theorem without replacing
   the public spec by a numeric term.
2. Adapt `WriterC.jet_secp_scalar_read_write.eval_scalar_read_write_canonical`
   to insert the actual in-place negate call. The actual reader yields
   `scalar_writer_initial_rep_from_reader`. Use `scalar_limb_rho_value`
   to discharge `eval_scalar_negate_canonical_owned`'s value premise.
   Its conclusion already supplies the writer's concrete owned rep.
3. Preserve the reader's frame invariant through negation using
   `invA_stable` and the helper's outside-scalar `lframe`. Derive the source
   frame's current cursor and Freeable permission from that same frame;
   do not assume preservation or successful freeing.
4. Follow normalize's actual public call-node, entry/source-copy and
   return/free modules. Inspect the exact scalar-negate AST, temp list and
   call layout first. Reuse only the proven matching allocations/copy/free
   contracts; public negation has an extra actual in-place call.
5. Finish `secp_jet_local_spec f_simplicity_scalar_negate (Word 8) (Word 8)
   (@canonical_scalar_negate Alg.CoreFunSem)` for every Word256. Extend the
   literal gate to that complete source statement, audit exact types,
   definitions and assumptions, and independently kernel-check it.
6. Assemble a separate normal namespace-C candidate only after the currently
   frozen scalar-zero acceptance run has ended. Review normal snapshots
   before full `check-jets.sh --accept`; no update/no-build shortcuts.

## Avoid repeated dead ends

- Bare `int_table secp_pure` execution returns `None` for the uint128
  shift-by-64 call. The helper uses the existing verified
  `secp_shift64_table` and `xfun_shift64_sound`; this is an actual Clight
  helper proof, not an assumed execution oracle.
- `eexists` did not determine the output-limb list from the length goal.
  Give the exact map of final-region cells as the witness.
- Do not dump full `vm_compute` output with Int64 proof records: it produced
  over 90,000 tokens. A scratch-only `negate_compact.v` shows constants as
  signed Zs. The real proof uses exact output equality and reusable carry
  contracts, not that diagnostic printer.
- Normalize closed powers in hypotheses as well as goals before `lia`.
  The inspected `scalar_limb_rho_value` mismatch was `value / 2^192`
  versus the explicit constant denominator, not a missing arithmetic fact.
- For the zero/nonzero mask, use `Int64.mul_zero` / `Int64.mul_one` after
  the boolean split. Reducing whole int records introduced different proof
  fields for equal representatives; reflexivity then failed.
- Preserve literal multiplication/mod512 and explicit `unit >>> scribe`.
  Internal numeric lemmas are bridges, never substitute public specs.

## Pending full acceptance

Session **45608** owns normal scalar-zero full acceptance under
`/tmp/jet-scalar-zero-accept.smyVL2`. It was revalidated live in this turn;
its latest log reports `coqchk passed on 804 modules` followed by
`== assumption gate`, after all earlier gates and normal build.
Poll that existing handle, never infer completion/restart from silence.
All its inputs remain frozen. Pre-acceptance fingerprint:
`c4027e45b7c0b61edc21ee42e2e72a64a79ff4465002033dc18be5bb0cfc8657`.
Candidate 356/533 is provisional until terminal exit zero and receipt review.

## Coordination

Claude's shared-obligations branch owns memcpy linkage, SHA startup,
shared-frame/Bit-Machine constructibility, and now proposes Elements
translation-unit foundations/getters. No overlap with this scalar caller.
Leave their new modules and worktree untouched. Shared registry integration
remains here; preserve existing mixed staged/unstaged work in the checkout.
