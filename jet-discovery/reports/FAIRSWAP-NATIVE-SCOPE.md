# Native FairSwap file sale

`app-fairswap-file-sale` passes all **24 native vectors**: eight accepting
lifecycle or fraud paths and 16 adverse cases. It is one full, bounded spend
condition for the **post-funding** lifecycle. Funding the initial accepted
output constitutes buyer acceptance. Party key setup, delivery of encrypted
file data, authorization of the separate fee input, and chain confirmation are
outside this spending predicate. Fresh shared costs and mining remain pending.

The primary source is Lisa Eckey's dissertation *Blockchain Scalability through
Secure Optimistic Protocols*, chapter 5, especially Algorithm 8 (Judge), §5.4.2
(contract), and §5.6 (file-sale circuit). The complete [author-hosted PDF](../vendor-specs/crypto-growth/fairswap-author-bitstream.pdf)
is vendored under its stated CC BY 4.0 license. The direct 2018/740 eprint PDF
returned HTTP 403; the [source manifest](../vendor-specs/crypto-growth/MANIFEST.md)
records both that gap and the successful university bitstream. The thesis links
`lEthDev/FairSwap`, pinned at `07f5664de64e232a0e1a8c0a84eefc223b45ae8b`
(2018-08-13). Its three files are inert data. No repository license was found,
and no downloaded code is executed.

The circuit has four 32-byte plaintext chunks at nodes 0–3. Nodes 4 and 5
are Keccak-256 of chunks 0||1 and 2||3 respectively. Node 6 is Keccak-256
of nodes 4||5, the agreed file root. Ciphertext at index `i` is the plaintext
word XOR `Keccak256(uint256_be(domain) || key)`. The domain is `i` for chunks
0–3 and `4+i` for internal nodes 4–6, matching the file-sale prototype with
four chunks and one word per chunk. The eight-leaf ciphertext tree holds
Keccak-256 of ciphertext at 0–3, raw ciphertext at 4–6, and a zero dummy at
7. Parents hash two 32-byte children; an opening has exactly three siblings.
Merkle positions and circuit wires are constants in the program.

The state commitment is SHA-256 of `FairSwapNativeV1`, one phase byte, then the
32-byte key commitment, ciphertext root, file root, and key. `Lib.State` binds
this value to a NUMS-derived Taproot internal key and one executable leaf.
Phase 0 carries a zero key; phase 1 carries the actual key. The protected
input must be **input 0**, with exactly two inputs and one output. Buyer and
seller keys, the price of 100,000 sat, and the ten-block relative lock are fixed.
Every transition authenticates the current state and preserves its full value
in either the continuing leaf or the designated party's script. Input 1 pays
fees under its own authorization.

| Current state | Action | Required evidence | Result |
|---|---|---|---|
| Accepted | Reveal key | Seller signature on native `sig_all_hash`; correct key commitment | Same leaf and value, committed revealed state |
| Accepted | Refund | CSV 10 | Fixed buyer payout |
| Revealed | Acknowledge | Buyer signature on native `sig_all_hash` | Fixed seller payout |
| Revealed | Delayed payout | CSV 10 | Fixed seller payout |
| Revealed | Root complaint | Buyer signature; authentic ciphertext node 6; decrypted root differs from agreed file root | Fixed buyer payout |
| Revealed | Gate 4, 5, or 6 complaint | Buyer signature; three authentic indexed openings; decrypted output differs from the hash of its actual circuit inputs | Fixed buyer payout |

Bitcoin CSV sets a lower bound on when a transaction is eligible. A delayed
revelation can race a refund, and a delayed complaint can race seller payout.
The native application assumes timely monitoring and confirmation. It does not
implement the Ethereum prototype's upper wall-clock deadlines.

Algorithm 8 authenticates the gate description and its input indices. The early
Solidity prototype lets callers choose `_indexOut` and `_indexIn` without the
corresponding wiring check. Its `vrfy` hardcodes three levels, accesses proof
positions 3, 2, and 1, and handles position 0 separately. The native verifier
uses the fixed valid circuit wiring and three bottom-up siblings. An independent
reference counterexample opens an honest gate 4 output with unrelated input
nodes 2 and 3: all openings authenticate, but the unrelated inequality would
cause a false complaint. The complete native verifier rejects that certificate.
This demonstrates the omitted relation; no downloaded Solidity was executed.

The input-index check protects both permissionless timeout paths. With two
identical 100,000 sat state inputs and one 100,000 sat payout, the earlier
branch relation accepted at both indices, leaving another 100,000 sat as fee.
`tools/FairSwapIndexProbe.hs` reproduced this for the accepted refund and the
revealed seller payout against genuine state scripts. The fixed branch accepts
index 0 and rejects index 1 in both cases: all eight checks passed, actual exit
0, 116.68981 seconds at a 4 GiB heap cap. The exact pre-fix full source is in
`reports/data/fairswap-before-index0/`; the branch reproducer and its logs are
separate from the full-sale proof. The full vector set also rejects the
index 1 transaction.

The executable binds the shared header once. Each selected action tag, role
signature, key, ciphertext, and sibling enters once at its consuming stage.
The derived plaintext and Merkle node flow as actual data; every opening uses
the same projected key and ciphertext root. The declarative `saleT` is retained
for relation review. The executable uses ordinary execution because it has
independent internal witnesses; it makes no prepared-path claim.

| Validation stage | Actual outcome | Wall seconds | Maximum live bytes |
|---|---|---:|---:|
| Independent Judge/wiring reference | PASS, exit 0 | 0.42924 | 172,936 |
| Seven indexed openings and three state commitments, 4 GiB cap | 10/10 PASS, exit 0 | 139.20326 | 3,351,027,128 |
| Complete sum-typed witness, 16 GiB cap | Construction exhausted heap before any vector, exit 251 | 96.46460 | 16,864,892,912 |
| Staged current 24 vectors, 16 GiB cap | Construction exhausted heap before any vector, exit 251 | 93.90499 | 16,866,165,200 |
| Staged current 24 vectors, seed forced before signed fixtures, 32 GiB cap | **24/24 PASS, exit 0** | **2,745.31480** | **25,690,039,712** |

These are validation resource measurements. The successful run held 33,281 MiB
in the RTS, including allocation overhead. Its unsigned canonical seed completed
in 91.668591 seconds, leaving 340,527,552 live bytes after a collection. Forcing
that existing commitment first separates its construction from signature
fixture generation. The signed fixture matched the seed CMR
`2b36765d6b549e8aad0a2b5dcc0dbf4bda30cdcb2145a5c4377e8da13747ce6f`.
The 32 GiB run changes both the cap and forcing order; it does not establish that
forcing order alone would make the full verifier fit 16 GiB.

The initial generic Keccak helper also exhausted a 4 GiB cap. The current
fixed 32- and 64-byte frontends encode the original Keccak `01`/`80` padding
directly into the state, run all 24 rounds, and extract the first 32 bytes.
They avoid retaining the original message beside the permutation. No existing
jet, primitive, or hash semantics changed.

Reproduce with `tools/FairSwapProbe.hs` modes `reference`, `helpers`, and `full`.
Use the direct GHC 9.8.4/package flags in [CRYPTO-FAMILIES.md](CRYPTO-FAMILIES.md)
and `-with-rtsopts=-T` for the full diagnostic. For the successful complete run:

```
python3 tools/run_crypto_validation.py --label FRESH-LABEL --binary BINARY \
  --build-dir BUILD-DIR --driver tools/FairSwapProbe.hs --heap 32 --group full \
  --compiler-flags '-O1 -threaded -rtsopts -with-rtsopts=-T -isrc'
```

The complete [verification log](data/fairswap-canonical32-full-verification.txt)
and [provenance](data/fairswap-canonical32-full-provenance.json) record actual
exit status, compiler settings, the binary SHA-256
`9a057331aef2a064f67f697c592f12fc0ead6fe91b688e2b787edd2982e599c8`, and all
33 frozen source files. No source changed during that execution. The failed
attempts and helper results are preserved under the other `fairswap-*` prefixes
in `reports/data/`. The native vector result qualifies one application; the
branch probes, file size, gate choice, and helper functions add no extra group.
