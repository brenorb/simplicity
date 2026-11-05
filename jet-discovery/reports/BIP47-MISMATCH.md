# BIP47 notification HMAC argument-order conflict

The pinned BIP47 sender and receiver prose give opposite HMAC argument orders. The full published vector and two independent primary implementations unambiguously use **key=raw serialized outpoint36, data=ECDH x32** for both roles. This is the explicit bounded interoperability target; no upstream file is corrected. We infer that the contradictory receiver notation is an ordering error, rather than claiming an upstream maintainer has issued an erratum.

| Evidence | Exact retained location | Behavior |
| --- | --- | --- |
|Normative sender steps|Growth3 `bip-0047.mediawiki:160`|Notation HMAC-SHA512(o,x).|
|Normative receiver steps|Growth3 `bip-0047.mediawiki:176`|Contradictory notation HMAC-SHA512(x,o).|
|Full BIP-linked vector gist|SamouraiDev gist `beddb67cf219ead27b8b1380a3b084b8dde51093`; entire6010-byte text retained|Exact outpoint/shared-x/mask, full signed notification and10 payment addresses. Standard key-first HMAC with outpoint key reproduces the mask.|
|Sparrow Drongo primary implementation|Commit `2c703d2048135b23c9faffe4c7cafc57768f26f9`, `PaymentCode.java:190–198`|The public helper's arguments are named sPoint,oPoint, but its Mac secret key is oPoint and its final data is sPoint. Caller at125 supplies ECDH bytes and serialized outpoint. Apache-2.0 source/license retained inert.|
|Dojo/Samourai package primary implementation|Commit `29746951b43bb40c4303fe56d63cffd76db58947`, `src/payment-code.ts:234` and406; `src/utils.ts:51–52`|Both sender and receiver pass outpoint as key and ECDH x as data to a wrapper explicitly named key,data, then standard HMAC. LGPL-3.0 source/license/archive retained inert; not linked or executed.|

The source URLs and every raw file hash/revision/license are in `bitcoin-growth7/manifest.json`. The BIP47 text and gist have no explicit standalone license statement; that metadata gap is retained. A complete pinned vector, rather than an excerpt/sample, is used. No downloaded Java/TypeScript is executed, and no upstream issue/message/correction is submitted.

| Input / output | Exact raw bytes |
| --- | --- |
|Outpoint key,36 bytes|`86f411ab1c8e70ae8a0795ab7a6757aea6e4d5ae1826fc7b8f00c597d500609c01000000`|
|ECDH x data,32 bytes|`736a25d9250238ad64ed5da03450c6a3f4f8f4dcdf0b58d1ed69029d76ead48d`|
|Published mask and independently computed key36/data32 output|`be6e7a4256cac6f4d4ed4639b8c39c4cb8bece40010908e70d17ea9d77b4dc57f1da36f2d6641ccb37cf2b9f3146686462e0fa3161ae74f88c0afd4e307adbd5`|
|Literal reversed key32/data36 output, incompatible|`793bb1ccc3eeb8c77d4e67ccf4c6c495f6c2c9cc7390dd580633eeca219c3042d13ecc8c3f05fe2bf55cf9a689db44e620898e47d4f6ea953ce2dae0e4e3bb37`|

Both actual Python stdlib HMAC outputs and original source hash are preserved in `bip47-hmac-order-comparison.json`. The raw36-byte key is the exact wire outpoint, including the final little-endian index1 (`01 00 00 00`), with no reversal of the raw32 hash. A generic `hmac36x32` takes raw byte-word fields; a native primitive caller must convert its **numeric index** with bswap32 before supplying that raw final Word32. The same conversion must never be applied to the native raw opHash. This follows the canonical C/Haskell API documented in `OUTPOINT-BYTEORDER.md`.

Source agreement resolves the bounded target without silently choosing one contradictory line. This evidence earns no application group; complete notification/payment-client implementation, private-client boundaries and actual native/source-vector tests remain separate gates. A public onchain disclosure of the notification ECDH/private material would undermine its intended privacy and is not invented as a native covenant.
