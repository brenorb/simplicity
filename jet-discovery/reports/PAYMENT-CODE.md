# BIP47 private notification and incoming-payment client

`app-bip47-notification-payment-client` passes all19 actual Simplicity vectors
under one canonical CMR:
`6db7a161cb69d345e7e3396f05404fdfce3a1114cc4a756f1698e6337c4ed4fb`.
This is one complete bounded **CLIENT MODE** verifier group. Receiver private
keys remain local client inputs; they are not a proposed public onchain witness.
No Bitcoin spend-budget feasibility or measured WU is claimed here.

The published v1/noBitmessage profile comes from
[BIP47](https://github.com/bitcoin/bips/blob/a0c977f3755da6476b955677ca9318334a2432c4/bip-0047.mediawiki)
and its complete linked
[SamouraiDev vectors](https://gist.github.com/SamouraiDev/6aad669604c5930864bd/beddb67cf219ead27b8b1380a3b084b8dde51093).
Growth7 retains the exact upstream snapshot and both primary implementation
comparisons. Its gist has no explicit license: that access/licensing gap remains.
Growth8 contains only local derived/reference data. Downloaded code was never run.

The native expression checks a canonical receiver private0 against Bob's actual
notification public key, computes ECDH with the source transaction's designated
input public key and HMAC-SHA512(raw serialized outpoint36, ECDH-x32), and binds
the recovered canonical Alice code by reconstructing and double-hashing the
**complete signed notification transaction**. It then derives Bob's selected
child with full HMAC-SHA512 CKDpub and checks its private key, derives Alice child0
with full HMAC-SHA512 CKDpub, computes SHA256(ECDH-x) as the payment scalar, adds
that scalar times G, and hashes the resulting compressed point to the actual
incoming P2PKH output. The current client transaction view must have one input,
one output atindex0 and exactly50000sats paid to that derived script. That amount
is this authenticated client request, not a BIP47-wide rule.

One structured1041-bit maximum witness carries private0, Alice code and a
sum-typed selection. Index0 reuses the same actual private0 field; indices1–9
carry one distinct child private key. Every reuse is a projection. The host
encoder rejects unrepresentable integers or wrong fixed header/reserved bytes;
native scalar/point/index checks still enforce the actual typed values.
HMAC37/CKD has local explicitly shared witness-free term kernels. There is no
whole-application compiled-DAG cache or repeated logical witness reopening.

| Published index | Exact source payment address | Actual native result |
| --- | --- | --- |
| 0 | `141fi7TY3h936vRUKh1qfUZr8rSBuYbVBK` | Accept |
| 1 | `12u3Uued2fuko2nY4SoSFGCoGLCBUGPkk6` | Accept |
| 2 | `1FsBVhT5dQutGwaPePTYMe5qvYqqjxyftc` | Accept |
| 3 | `1CZAmrbKL6fJ7wUxb99aETwXhcGeG3CpeA` | Accept |
| 4 | `1KQvRShk6NqPfpr4Ehd53XUhpemBXtJPTL` | Accept |
| 5 | `1KsLV2F47JAe6f8RtwzfqhjVa8mZEnTM7t` | Accept |
| 6 | `1DdK9TknVwvBrJe7urqFmaxEtGF2TMWxzD` | Accept |
| 7 | `16DpovNuhQJH7JUSZQFLBQgQYS4QB9Wy8e` | Accept |
| 8 | `17qK2RPGZMDcci2BLQ6Ry2PDGJErrNojT5` | Accept |
| 9 | `1GxfdfP286uE24qLZ9YRP3EWk2urqXgC4s` | Accept |

All ten cases also pass an independent byte/Integer Haskell reference: two account
roots, all11 published child private/public pairs, all ten raw ECDH-x values,
their separately derived SHA256 payment tweaks, all ten Base58Check address
scripts, the complete source notification signature and all ten newly signed
standard P2PKH payment transactions. The uppercase source labels `S_i` denote
raw ECDH-x, not SHA256(x); `bip47-all-payments.tsv` retains both named fields.
The failed preliminary local label comparison is preserved in
`payment-code-reference-shared-label-failed-rts.txt`; it is not an upstream bug.

The nine same-CMR negatives reject wrong/noncanonical private0, changed valid
Alice public key, changed Alice chain code, wrong/noncanonical selected Bob
private key, a fresh valid payment to a different payee, a fresh valid underpayment,
and an alternative index0 key-field encoding. The payment negatives are signed
again, so a stale transaction signature does not mask the payment relation.
All outcomes ran through the actual canonical prepared-kernel path, which checks
each input type and whole-program commitment root against the measured program.

`reports/data/payment-code-full16g-rts.txt` records exit0 and19/19PASS,
470.221s RTS elapsed,12,035,865,624B maximum live residency and16643MiB total
RTS memory at`-N1 -M16G`. This is execution/CMR evidence, not an application cost
measurement. `payment-code-full16g-provenance.json` hashes the exact dependency
closure, input data, executable and log, with source snapshots under
`payment-code-full16g-freeze/`. Sources were unchanged throughout the run. The
same executable is retained outside the Git tree at the recorded relocation path.
After completion only the report classification string changed from
`PRIVATE CLIENT MODE:` to canonical `CLIENT MODE:`; the exact one-line diff and
pre/post source hashes are in`payment-code-metadata-prefix-change.json`.
The predicate, type and CMR are unchanged.

`payment-code-reference-rts.txt` records the complete independent source/wire
check (exit0,3.506s). `hmac-byte-reference-rts.txt` records64 independent SHA512/
HMAC checks: all50 cases matching the separately tested native helper cohorts,
plus eight padding boundaries and six HMAC key-length boundaries. The byte/Word64
reference does not evaluate the native HMAC expression. Its extra input packets
were independently generated with Python stdlib hashlib/hmac.

The raw outpoint hash remains exactly the32 wire/digest bytes exposed by both
actual C `input_prev_outpoint` and the Haskell primitive. Only the numeric index
is converted to its four little-endian bytes before HMAC. All ten generated
payment wires and the source notification also pass actual C/Haskell primitive
checks. Explorer display txid reversals are confined to the named source display
comparison. The sender/receiver HMAC-order prose conflict and both differing
outputs are retained in`BIP47-MISMATCH.md`; the implemented deployed profile
matches the full published vectors and both pinned primary implementations.

The client authenticates the prior notification bytes/txid and the current
incoming-payment primitive view externally. It does not prove chain inclusion,
UTXO existence, finality, normal transaction validity or a human sender identity.
The source notification input's previous amount is not published; its legacy
signature check needs the supplied source script but not an invented amount.
BIP39 setup, hardened account creation, Base58 transport and higher indices /
other feature profiles remain outside the native bound. All source account and
address transport records are nevertheless inventoried and reference-checked.

Reproduce the input extraction and integrity check with
`python3 tools/extract_bip47_vectors.py` and
`python3 tools/check_bitcoin_growth8_packet.py`. Compile the local
`tools/PaymentCodeReference.hs`, `tools/HmacByteReference.hs` and
`tools/PaymentCodeSmoke.hs` with the cached GHC package database and`-isrc`.
Run the reference tools at`-N1 -M512M -s`; run the full client at`-N1 -M16G -s`.
The exact standalone build/run paths and frozen source snapshot accompany the
provenance. Registration and the shared full-corpus analysis are separate steps.
