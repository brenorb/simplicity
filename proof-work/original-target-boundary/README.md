# Original Bitcoin target: domain/identity and stale-object diagnostic

The production/original-specification source guard passes (240 pinned files).
The existing Bitcoin identity gate fails: the unchanged starting Coq module
uses `locktime`, while the unchanged Haskell primitive uses `lockTime`. No
source, API or gate is changed by this diagnostic. It adds zero jet coverage.

`OriginalBitcoin.v.source` is byte-identical to
`91d89bac:Coq/Simplicity/Primitive/Bitcoin.v` and to the current original source.
It was explicitly compiled in the separate `TargetReview` namespace. Five
closed facts in `OriginalDomainBoundary.v.source` establish that this original
domain excludes empty outputs, an input amount with bit 63 set, and a transaction
with total input 10 and total output 9; its primitive name is `locktime` and is
not `lockTime`. They classify why some newer domain checks/identity checks cannot
be transferred to the original target. They do not prove a C execution, a fee
jet mismatch, a commitment-hash inequality or an implementation bug.

The new issuance local/constructibility chain does not load the old Bitcoin
module. The hash chains do. Their existing kernel receipts remain historical
evidence for their exact compiled inputs, but the claim that all dependencies
were rebuilt from the restored sources is not justified by incremental make.
Separate forced full-local-closure builds are in `../elements-issuance-clean`
and `../elements-hashes-clean`. They do not overwrite the earlier receipts or
alter the original targets. Whole-repository acceptance/registration remains
unresolved; the failed identity gate is not relaxed.
