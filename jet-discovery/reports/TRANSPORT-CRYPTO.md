# Bitcoin transport cryptographic components

Three component families implement their complete bounded primitive. They
receive one counting group each and no full-application credit. All116 actual
Simplicity vectors pass, with an unchanged jetted CMR within each family.
These public-witness expressions measure computational demand; a public MAC
key or cipher key supplies no confidentiality or secret-key authentication.

| Family / exact interface | Complete published set inspected | Additional controls | Actual vectors |
| --- | --- | --- | ---: |
| SipHash-2-4,64-bit result,128-bit key,0..511 message bytes | All64 SipHash64 KATs at veorq/SipHash revision `32d067603b93b47828700880649198e0bfbbcffa` | Seven derived lengths64/65/127/128/255/256/511; three corruptions |74 |
| ChaCha20 full block,256-bit key,96-bit nonce,32-bit counter | All6 complete RFC8439 block KATs: section2.3.2 and appendixA.1 | Counter0/1/maximum controls; three corruptions |12 |
| Poly1305,raw256-bit one-time key,0..511 message bytes | All12 RFC8439 MAC KATs: section2.5.2 and appendixA.3 | Fourteen length boundaries, clamp invariance, three corruptions |30 |

The full SipHash128/HalfSipHash variants, ChaCha cipher/AEAD vectors and
transport-session state machines are outside these interfaces. They are not
silently counted as tested. RFC4231 is retained as a source for possible HMAC
work and contributes no implemented group or vector here.

SipHash handles little-endian key/message words, every tail length, two
compression rounds, four finalization rounds and the low8-bit message length
in the terminal word. ChaCha uses all20 rounds, the specified column/diagonal
schedule, feed-forward and little-endian output. Poly1305 clamps r, inserts
the partial-block marker, reduces modulo2^130−5 after each block and adds s
modulo2^128. Its wide products check the unused high half; no inverse,
quotient or accumulator hints are supplied.

`Ref.SipHash`, `Ref.ChaCha20` and `Ref.Poly1305` are independent Haskell
arithmetic references. `tools/extract_transport_vectors.py` parses the
vendored primary text as inert data, checks exact set counts/widths and emits
the complete KAT TSVs. It never compiles or executes the downloaded C/header.
The packet's `manifest.json` records8 primary files with URLs, revisions,
licenses and SHA256; `derived-manifest.json` pins all3 extracted TSVs.

The complete three-family run is preserved in
[transport-complete-three-families.json](data/transport-complete-three-families.json)
and its adjacent text log: successful exit,77.050seconds,3GiB heap cap.
The shared executable also passes all three complete groups in
`transport-shared-siphash`, `transport-shared-chacha` and
`transport-shared-poly1305` JSON/text records. These are vector-only results;
the common final cost/mining/overlay/ablation run remains required.

Build the normal project, then run `jet-discovery verify crypto-siphash24`,
`jet-discovery verify crypto-chacha20-block` and
`jet-discovery verify crypto-poly1305` from this directory's project root.
`tools/TransportCryptoSmoke.hs` supplies the standalone cohort. Local compiler
objects and binaries are excluded from the source packet.

`Lib.HmacSha512.hmac37` is an auxiliary RFC2104 HMAC-SHA512 implementation
for exactly32-byte keys and37-byte data in the BIP32 CKDpub shape. It uses
all4 SHA512 compressions, including full inner/outer padding; no midstates
or digests are supplied as hints. All20 independently generated Python
stdlib `hmac`/`hashlib.sha512` derived cases and5 changed key/data/digest
negatives pass actual Simplicity evaluation at one canonical CMR. The
successful8GiB-capped run takes195.755seconds and is preserved in
`data/hmac-sha512-37-helper-vectors8g.{txt,json}`; its earlier3GiB construction
failure remains separate. These are derived vectors, not RFC4231 KATs.
`tools/generate_hmac37_vectors.py` and its separate derived manifest pin
that packet. The helper validates hashing only; BIP32 prefix/index/point and
wallet policy belong to its caller. It earns no additional corpus group.
