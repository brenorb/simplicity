# BIP347 bounded OP_CAT

`bip347-op-cat` checks the byte relation `left || right` on two
supplied stack elements and a claimed result. The left input represents
the element below the top of the Script stack. Each operand can have
zero through 520 bytes. The expression rejects a sum greater than 520.
BIP347 also specifies stack underflow and activation behavior. This
component's typed input supplies two elements, so those Script rules,
policy and surrounding opcodes are outside its scope.
[Pinned BIP347](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0347.mediawiki)

An element is a 16-bit byte length and a balanced 1,024-byte word.
Logical byte zero occupies the least-significant byte, including when
it is zero or its high bit is set. An operand is canonical when the
declared length is at most 520 and every byte beyond it is zero. The
check follows the length boundary down the balanced storage tree and
checks unused halves for zero. The two checked lengths fit their
16-bit sum. After checking the result
limit, the kernel shifts the right word left by the left length in
bytes and ORs it with the left word. The words occupy disjoint byte
ranges, and both ranges fit inside the storage. The kernel compares
the computed length and the entire computed word to the claim, which
also enforces the result's canonical tail. All lengths and bytes enter
through one typed witness and remain actual data through every use.

The measured assertion includes the input guards, both canonical-tail
checks, the concatenation and the result equality. The
encoding is a fixed-capacity study interface. Its program and witness
sizes apply to this component's padded representation. The
independent Haskell reference operates directly on byte strings.

## Published vector coverage

The BIP publishes three inline Script cases and points to Bitcoin Core
PR 29247 for the extended suite. The packet pins the PR author's head
`6ca33cb59e4a1526fb6fd74d0bc84aaa35e3fccd`. It retains the full
1,305-row JSON file, relevant unit and functional test sources and
their MIT license as inert data. All three inline BIP rows exactly
match JSON rows 1191, 1200 and 1207 in the pinned suite.
[Bitcoin Core proposal](https://github.com/bitcoin/bitcoin/pull/29247)
[Source revisions, licenses and hashes](../vendor-specs/bip347-cat/manifest.json)

| Published test source | Coverage in this component |
| --- | --- |
| JSON script tests | All 34 CAT-related rows inventoried. The 18 rows with executed CAT and two operands project to 33 typed relations, including intermediate steps in repeated or chained cases. The 16 remaining rows are headings, activation or discourage-policy checks, a script that does not run CAT, or stack underflow. |
| C++ `cat_simple` and `cat_empty_stack` | Both inputs and exact results projected. |
| C++ `cat_dup_test` | All 260 actual inputs to `DoTest` projected. The pinned code breaks before that call when its precomputed result exceeds 520, and breaks after its first success. Its outer loop visits sizes 1 to 522. The native upstream test invocation therefore exercises one doubling for each input length 1 to 260. |
| Python `feature_opcat.py` | Three policy/activation checks on default Tapscript, SegWit v0 and P2SH contexts. These test node and Script behavior outside the value relation. |

The two wrong-result JSON cases become failed equality claims. The
four `PUSH_SIZE` JSON rows become size rejections. Where the source
only checks successful Script evaluation, the fixture takes the
actual operands from the source and computes the expected result by
byte concatenation. The full per-row scope and the exact typed input,
output and outcome for each projected operation are retained below.
[All CAT-related JSON rows](../vendor-specs/bip347-cat/script-json-inventory.tsv)
[All 295 typed upstream projections](../vendor-specs/bip347-cat/relation-vectors.tsv)

The corpus adds 47 vectors for order, exact byte and size boundaries,
including 0, 255, 256, 511, 512, 519, 520 and 521 bytes. Malformed
claims cover a nonzero tail in each operand and the result, high
length bits, swapped operands and the wrong length or bytes. The
standalone driver additionally evaluates the typed value expression
against the byte reference for every split summing to 520, and every
split summing to 521 with both operands individually legal.

## Native measurement

All 342 claim vectors passed under CMR
`e894f438bc04da2ef3fc73fbe8c219189690f9a494f007cf0f1a2b67d7835140`.
The same program accepted 322 cases and rejected 20. The runner checked
the canonical CMR on each vector, the profile sum against the measured
bound and the final profile root against the canonical CMR.

The retained core log is the exact prefix through the completed
corpus and static-analysis checks. The launch snapshot records the
executable and input hashes at that point. At capture, the optional
1,041 direct split checks were still running. The partial launch
record carries no terminal exit status or RTS statistics.
[Completed core log](data/bip347-cat-core342.txt)
[Core evidence hashes](data/bip347-cat-core342-provenance.json)
[Partial launch record](data/bip347-cat-core342-partial-launch.json)

The diagnostic subsequently completed both direct split batches and
exited successfully. All 521 splits totaling 520 bytes returned the
reference bytes, and all 520 splits totaling 521 bytes with legal
operand lengths rejected. Across the entire diagnostic, the host RTS
reported 2,011.955 seconds elapsed, 5,955,801,712 bytes maximum
residency and 12,479 MiB total memory in use.
[Terminal vector and RTS log](data/bip347-cat-tail-tree-full342.txt)
[Terminal launch and result hashes](data/bip347-cat-tail-tree-full342.json)

| Quantity | Value |
| --- | ---: |
| Native static bound | 8,793.377 WU |
| Primitive-only static bound | 112,123.527 WU |
| Combined candidate overlay, ESTIMATE | 8,793.377 WU |
| Serialized program | 25,973 bits |
| Serialized witness | 24,624 bits |
| Jet-substituted DAG | 1,665 nodes |
| Hypothetical witness-stack budget | 6,449 WU |
| Deficit in that scenario | 2,344.377 WU |

The fixed four-element stack occupies 6,399 bytes in the study's budget
scenario, including the CMR, control block and CompactSize fields.
This is the cost of the padded CAT equality claim, including its
validation and comparison. The comparison does not price a new opcode
or candidate jet. [Budget method](METHOD.md)

## Reproduction

Run from `jet-discovery/`. The projection reads the pinned bytes and
does not execute the downloaded code.

```sh
python3 tools/project_bip347_vectors.py --check
ghc -O1 -w -threaded -rtsopts -isrc \
  -package-db dist-newstyle/packagedb/ghc-9.8.4 -package jet-discovery \
  -outputdir /private/tmp/bip347-cat-build tools/Bip347CatSmoke.hs \
  -o /private/tmp/bip347-cat-smoke
python3 tools/run_recorded.py bip347-cat-tail-tree-full342 -- /private/tmp/bip347-cat-smoke \
  +RTS -N1 -A16m -M16G -s -RTS
```

The corpus module and diagnostic driver use local GHC optimizer
settings to keep the wide balanced Haskell type dictionaries
manageable. Simplicity jet substitution and cost measurement use
the ordinary corpus runner.

Two earlier encodings used full-width right shifts for the input
tail checks. Both reached the 8 GiB heap cap before a CMR or vector
result. The unsuccessful logs and exact kernel sources are retained.
[Generic barrel run](data/bip347-cat-full342.txt)
[Generic barrel source](data/bip347-cat-first-kernel.hs.txt)
[Ten-stage barrel run](data/bip347-cat-shared-full342.txt)
[Ten-stage barrel source](data/bip347-cat-shared-kernel.hs.txt)
