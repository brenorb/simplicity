# Original issuance entropy, asset and token getters

Four complete candidate modules provide the three actual getter-call contracts
`elements_issuance_entropy_local_spec`, `elements_issuance_asset_local_spec`
and `elements_issuance_token_local_spec`. These are the original inline getters
in `C/elements/elementsJets.c`, not the separate `calculate_*` C jets.

The specification dependencies are literal core programs from
`Haskell/Core/Simplicity/Programs/Elements.hs` and the three primitive-based
programs from `Haskell/Simplicity/Elements/Programs/Issuance.hs`. In particular,
new entropy includes the outpoint double-hash, its byte-swapped index and
original block constants; reissuance uses ReissuanceEntropy. Asset and token
reuse that program. Token selection distinguishes confidential and explicit
IssuanceAssetAmount exactly as the original nested case program does.

The four modules compiled in the scratch `IssuanceCanonical` namespace, with
full reports for 25 results and 29 definitions: 15 closed, three using only
functional extensionality, one using the four inherited expression dependencies,
and six using the six inherited execution dependencies. No new axiom, assumed
execution or desired output was added. The archived imports are now rebased to
the ordinary `C` namespace; its independent forced rebuild is a separate check,
not a transfer of the scratch receipt.

The final contracts derive allocation, source-frame copy, index read, both tag
cases, cached hash writing/padding, return/free, encoded output, prefix, cursor
and outside-memory observations from the existing separated-frame contract.
One shared execution proof is specialized to entropy/assetId/tokenId. Actual
AST field checks establish issuance-relative offsets 72/168/200; these are not
the intervening range-proof cache offsets 104/136.

The explicit initial `computed_issuance_hash_rep` still requires the represented
issuance enum and the cached words of the canonical value when present. The
normal caller must establish that relation. These modules do **not** prove
that the production Elements environment builder computes those caches, or
that the separate `calculate_*` C jets implement the calculation programs.
No monetary, issuance-kind or nonempty-array restriction was introduced.

## Verification and continuation

After a successful compilation, run:
