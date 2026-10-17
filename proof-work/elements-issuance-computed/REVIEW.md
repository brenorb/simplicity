# Scoped contract and source review

This is review evidence for these candidates, not whole-repository acceptance.
No accepted coverage is changed.

The target functions are the three original `simplicity_issuance_entropy`,
`simplicity_issuance_asset` and `simplicity_issuance_token` bodies. Their C
comments say TWO^256, but the actual code, generated bodies and canonical
catalog consume a 32-bit input index. The theorems use Word32. The unchanged
comments are not treated as specifications or corrected by this work.

The final `application_jet_local_spec_sep` conclusions retain the actual
`Clight2.eval_funcall` of the concrete original function, successful return,
encoded output, prefix, cursor and outside-memory observations. The existing
wrapper theorem derives entry, allocation, source copy and free. Generic
shape, field, presence and semantic hypotheses are discharged at each concrete
endpoint; they are not additional assumptions on its caller.

The initial relation names the enum load at input-record offset 528 and the
canonical cached hash words only when an issuance exists. It assumes neither
the jet call nor its final output. It is nevertheless a substantive **caller
cache obligation**: proving the original cache getters under this relation
does not prove the real builder fills those caches. That distinction must
remain in any future registry or completion claim.

The memory argument preserves cached words across the tag write using the
existing output/environment interval separation. It does not assume those
loads separately in the intermediate memory. Original arbitrary-output and
cursor/framing predicates are retained; no zero-initialization, fixed input,
new-only or reissuance-only restriction was added. This is not a new proof of
API aliasing behavior outside those existing frame contracts.

Source correspondence was inspected against the unchanged Haskell programs:

- `Programs/Elements.hs`: opHash keeps its nested SHA compressions, the four-byte
  index reversal, `2^31`, zero64, 288-bit length and `2^255 + 256` second-block
  constant; calculateIssuanceEntropy pairs the outpoint hash with the contract.
  Asset and token calculations use the original zero/`2^248`/`2*2^248` suffixes.
- `Elements/Programs/Issuance.hs`: entropy retains all three primitives and the
  original nested match/flip-match structure. Asset composes that entropy
  program. Token also pairs IssuanceAssetAmount, keeping every original missing
  input/issuance branch and confidential-versus-explicit selection.
- `Term/Core.hs`: `oh` is take iden and `ih` is drop iden; the index-reversal
  projections and match-arm order were checked using those definitions.

Actual AST field checks, not field-order guesses, discharge 72/168/200 for
entropy/assetId/tokenId. The intervening 104/136 fields are the range-proof
hashes. Separate shape lemmas check each concrete generated wrapper.

Full reports cover all 25 results and 29 definitions. The 15 closed results,
three reader-semantics functional-extensionality results, one four-dependency
expression result and six six-dependency execution results are checked
individually. There is no new axiom or skipped kernel check. A successful
forced rebuild and the 211-module loaded-source/object snapshot exist;
recursive checking completed with exit 0, with its own terminal receipt and
all local hashes unchanged before/after. External pinned libraries remain the
inherited trust boundary. Caller-cache establishment and normal registration
remain open; this is not full goal completion.
