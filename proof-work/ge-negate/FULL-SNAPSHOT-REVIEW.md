# Complete affine candidate snapshot reconciliation

Normal-load-path build 96488 and sequential full generation 90113 exited 0.
The point-negate baseline's full acceptance 77601 also exited 0. The affine
full snapshots have now been reviewed before acceptance, not merely updated.
FULL-SNAPSHOT-REVIEW.json records every count and both actual snapshot hashes.

- Removing exactly the 109 new type and 37 new definition records recovers
  the inherited contract snapshot byte-for-byte, including internal repeated
  displayed names and two inherited duplicate inventory rows.
- All 3946 inherited per-result axiom sets are unchanged. Every one of the
  109 new sets matches its independently reviewed actual Print Assumptions
  report. No additional assumed execution/output/free/library model appears.
- All 146 new contract records match the reviewed deep report modulo whitespace
  and explicit previously reviewed printing qualifications. The same one type/
  eight computed-definition supplements apply; retained text is diagnostic,
  not equality certification for omitted terms. Actual source/kernel evidence
  and scope review remain independently required.
- All 948 inherited whole-project sources, 38 new proofs, two new checkers and
  eight infrastructure hashes are unchanged. Extra candidate modules reject.

Read-only reproduction:

```sh
python3 proof-work/ge-negate/review-full-snapshots.py --work /tmp/jet-ge-negate.aFl8mr
```

The public proof is the original C simplicity_ge_negate with real source copy,
16+88 allocations, read_ge/ge_neg/write_ge calls, literal encoded output, true
return and both frees, under the unchanged inherited local-frame contract.
It applies to arbitrary Word256 pairs, without a curve-membership premise.
General evaluator/all-frame scope remains open; no every-jet completion claim.

Full isolated acceptance **13065 exited 0** with no update/no-build flags:
766 kernel modules, 4055 audited results/2107 closed, contract and negative
gates, all four generated ASTs. The post-run fingerprint is identical to
e07f8b9914471ba13bb9e67d3a676b35667b5f6881f48e30e985f2325d88ce7d;
post-run source guards and this full snapshot review pass unchanged.
`ACCEPTANCE.json` pins the terminal log. Candidate 355/533 is accepted only
for this isolated configuration and inherited local-frame scope; it is not
checkout integration or every-jet completion. Keep the candidate immutable
as the reference baseline; do not restart the completed run.
