# Canonical-source review: sixteen Bitcoin hash programs

This directory supplements the compiled and recursively kernel-checked proofs
in `../bitcoin-raw-program/`. It does not replace those proofs, establish the
Haskell host runtime, register coverage, or prove the C environment builders.

Run against the immutable proof tree:

```sh
python3 -B proof-work/bitcoin-raw-program-source/check-source.py /private/tmp/jet-bitcoin-raw-program.9b5hGOH3
python3 -B proof-work/bitcoin-raw-program-source/test-source.py /private/tmp/jet-bitcoin-raw-program.9b5hGOH3
```

Both commands passed; the second rejected 328 read-only source corruptions.
The fixed model is a `.py` file so that deploying these guards under `Coq`
includes the model in the normal source fingerprint. It is not regenerated
when checking a candidate. Reuse the previously reviewed TapLeaf/word/hash/SHA
guard dependencies during deployment; do not silently omit their model files.

## Reviewed implementation-to-specification chain

The C functions are actual cache getters, not C implementations of the hash
loops. Their complete checked contracts require the cached field to equal
the corresponding hash of the represented raw environment. The new shared
transport retains that obligation, separated frames, output cells, cursor
updates, prefix preservation and preserved loads. No final endpoint takes
the desired C execution or output as a new assumed premise.

`raw_full_sem` uses the existing Bitcoin primitive signature: base primitives
read `raw_base`, while extended script/annex/scriptSig primitives hash their
raw bytes. `project_raw_environment` constructs the cached logical environment
from those same bytes. `bitcoin_program_raw_projection` relates the **same
parametric Simplicity program** across both interpretations, through all nine
Core operations, assertions, failure and every primitive. Each concrete C
endpoint supplies its existing execution proof and proved parametricity.

The model pins the complete declarations, endpoint statements, representation
functions, algebra relation and raw projection, not merely selected words in
comments. The formal evidence reviewer separately checks actual compiled
sources/objects, reporting drivers, full printed types and definitions, exact
assumption sets, original-C AST regeneration and recursive kernel success.

## Canonical program correspondence reviewed

All sixteen catalog dispatches and unpacked-library selectors route to
`SigHash.lib`. The selected complete `mkLib` body is compared with the literal
Coq programs, including their local helper specializations:

| Programs | Bytes/element | Counter | Primitive/helper |
| --- | --- | --- | --- |
| Output/input values | 8 | 32 bits | OutputValue / InputValue |
| Output/input scripts, input scriptSigs | 32 | 32 bits | Corresponding script-hash primitive |
| Input sequences | 4 | 32 bits | InputSequence |
| Tappath | 32 | 8 bits | Tappath |
| Input outpoints | 32 + 4 | 32 bits | InputPrevOutpoint / outpointHash |
| Input annexes | 1 or 1 + 32 | 32 bits | InputAnnexHash / annexHash |

`hash_words_spec` initializes, runs the same `hashLoop`, and finalizes.
`for_while_program` matches both `SingleV` visits and the nested `DoubleV`
recursion of canonical `forWhile`, with the same early-stop branch. Empty
arrays finalize the initial context. The general element loop preserves both
early-stop and counter-exhaustion finalizers. The list truncation at the
counter's full range is explicit; it is not a sampling proof.

`outputsHash` and `inputUtxosHash` hash their two components in order.
`inputsHash` adds outpoints/sequences (64 bytes) then annexes (32 bytes).
`txHash` adds version/locktime (8 bytes), inputs/outputs (64 bytes), then input
UTXOs (32 bytes). `tapEnvHash` adds tapleaf (32 bytes) then tappath/internal key
(64 bytes). `sigAllHash` adds transaction/tap environment (64 bytes) then
current index (4 bytes). The literal tagged TapLeaf program, its computed ASCII
tag prefix and SHA context helpers reuse the preceding reviewed proof/guard.

## Representation edge cases

- Annex indexing distinguishes an absent input from a present input with no
  annex; only the latter hashes the single zero tag. A present annex hashes a
  one tag followed by its digest. The primitive has a nested optional result.
- `tappath` uses an unsigned 8-bit index. The existing represented environment
  still requires path length at most 128. No stronger or unrestricted caller
  contract is claimed.
- Haskell values are native unsigned Word64 and version is native Word32.
  Existing checked `word64_signed_unsigned` and
  `bitcoin_version_word_signed_unsigned` cover the Coq signed-carrier spelling
  for **all** bit patterns, including high-bit values. No monetary-range premise
  or positive-only restriction is added.
- `Schnorr.PubKey` here wraps a native Word256, not a normalized field element
  or a point. The reviewed four-limb unsigned decoder and
  `haskell_encode_pubkey_matches` link that encoding to `from_hash256`. There is
  no unproved public-key validity assumption hidden in this correspondence.
- Raw redeemed scripts, annexes and scriptSigs are bytes, not arbitrary hash
  inputs. Their projection hashes those bytes; it does not establish that all
  actual C allocation/building callers populate the required caches.

Two pure results are closed. Four pure Reader-algebra/relation results depend
on the existing dependent-functional-extensionality principle. All sixteen
whole-C endpoints have exactly the six inherited execution assumptions, not
an additional crypto oracle, execution axiom, or library-model premise.

Normal registration and full acceptance remain separate work. Current main
proof inputs are frozen while the actual-main420 audit runs; these review
files do not change them or the original staged patch.
