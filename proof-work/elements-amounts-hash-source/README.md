# Canonical source review: both amounts-hash jets

`SOURCE-REVIEW.json` records the actual successful positive comparison and
139 active, read-only source-corruption tests for the private amounts-hash
tree. All tests completed with exit zero. This phase does not register jets,
replace kernel checking, establish the real caller's caches or add coverage.

The fixed model pins66 complete Coq definitions/theorem statements and seven
canonical Haskell program blocks. It includes both complete public C-to-spec
contracts, their exact generated functions/global environment, result type,
cache relations and offsets24/248. It also checks the original C getter
bodies, four primitive bindings/carriers, wrappers and jet-catalog entries.
Signatures are compared as complete lines, not just matching prefixes.

The reviewed correspondence follows the actual program structure:

- `Transaction.outputAmount`/`inputAmount` pair amount then asset primitives,
  returning the asset/amount pair only when both indexed values are present;
- `assetAmountHash` absorbs the asset before the amount;
- asset tags are10/11 (confidential) or1 (explicit), followed by32 bytes;
- amount tags are8/9 (confidential,32 bytes) or1 (explicit,8 bytes);
- the32-bit indexed loop and both finalization branches reuse the checked
  generic hash-loop program and tagged-word absorber.

Confidential coordinates retain the existing packed-field projection boundary.
The check does not assert that arbitrary Word256 values are valid field
elements, or prove equivalence of host-language crypto/lens libraries. The
existing caller-cache relation remains explicit in both C theorems.

Two checker-development failures were resolved before recording success:
appending garbage to a carrier signature originally passed a substring check,
so it was strengthened to a full-line comparison; that comparison's selector
was then restricted to colon-bearing declarations so interpretation clauses
with the same constructor name are not treated as competing signatures.
Neither change altered the proofs, canonical sources or assumption allowance.

The model was created once after inspecting the sources; no checker regenerates
it from a candidate. The inherited nonce source-review tools and receipt remain
unchanged. Run the read-only checks with:

```sh
python3 -B proof-work/elements-amounts-hash-source/check-source.py /private/tmp/jet-elements-amounts-hash.66_lhzdf
python3 -B proof-work/elements-amounts-hash-source/test-source.py /private/tmp/jet-elements-amounts-hash.66_lhzdf
```
