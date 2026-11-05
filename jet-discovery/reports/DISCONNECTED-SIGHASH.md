# Shared outer CMR with distinct sighash modes

The default signature baseline and BIP118-style rebindable signature use the
same outer key and `checkSigVerify'` expression. The in-tree
[`CheckSig.hs`](../../Haskell/Core/Simplicity/Programs/CheckSig.hs) explicitly
disconnects its hash mode, so that mode does not affect the outer CMR.
The two entries measure different actual predicates. They are not parameter
sweeps or two versions of an identical signature statement.

| Actual expression | Identity of witness-free hash mode |
| --- | --- |
| `baseline-p2pk-sigall` | `ef3a6cfbf9153697fe5f7bde23fb9b3b7f9d875a4bfba84ef42a96fde59c268c` |
| `bip118-apo` | `16c9d7dc0d0d9918f130827bbb0a67deea1cd0e4659bff34956a690bc7077804` |

The actual outer CMR of both entries is
`f38dd7cdb4dd022d30b7b410fac0c70e74802cd2803f55455cfd55b81aeef6d5`.
With two otherwise identical transaction environments, changing the current
input outpoint changes the actual default digest and leaves the actual APO
digest equal. The [probe log](data/disconnected-sighash-identities.txt) and
[run record](data/disconnected-sighash-identities.json) verify both identities
and this difference (actual exit 0). The probe uses the original registry
entries for their outer CMRs and the real mode expressions for evaluation.
This is the one permitted identical-CMR pair in the final group audit. The
BIP118 entry still uses a native digest and is outside exact BIP341 wire scope.
