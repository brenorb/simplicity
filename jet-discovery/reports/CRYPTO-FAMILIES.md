# Crypto component families and WebAuthn wallet

Each component family counts at most once, independently of parameters, modes, input lengths or boundary vectors. Four component families and one native wallet are scoped here. Only a complete current vector batch with actual exit0 qualifies as passed. Reference-only success and compression-only success do not qualify the complete program. Runtime/residency below are validation resource measurements, never Simplicity costs. Fresh cost/what-if/mining rows remain **PENDING** until the common corpus analysis runs.

| Program ID | Scope | Complete vector evidence | Exit / seconds / maximum live bytes | Current source matches frozen executable? |
|---|---|---|---|---|
| `crypto-blake3-tree-hash` | component | 0/22 observed; **PENDING / NOT QUALIFIED** | FAILED exit251 / 81.04052441700333 / 16,871,401,528 | CHANGED: src/JetDiscovery/Corpus/Blake3.hs |
| `crypto-shake256-xof` | component | 17/17 observed; **PASS** | EXIT0 / 1428.5671603750015 / 13,137,127,680 | yes |
| `crypto-ml-dsa-ntt256` | component | 15/15 observed; **PASS** | EXIT0 / 309.43446866700106 / 3,051,781,120 | yes |
| `crypto-poseidon2-koalabear16` | component | 14/14 observed; **PASS** | EXIT0 / 44.56665737499861 / 981,571,296 | yes; unused parseRawTx-only correction; builder functions identical |
| `app-webauthn-counter-wallet` | full_spend_condition | 17/17 observed; **PASS** | EXIT0 / 2551.96916375 / 14,832,831,992 | yes; unused parseRawTx-only correction; builder functions identical |

## Exact relations, test coverage and deployment paths

| Program ID | Checked relation | Vector inventory / gaps | Bitcoin path and limits |
|---|---|---|---|
| `crypto-blake3-tree-hash` | Unkeyed BLAKE3,0–2048bytes→32bytes; all7rounds, blocks/chunks, real two-chunk parent/root | All19supported official unkeyed KATs;3length/canonical-padding/output negatives. All35upstream cases/all3modes inventoried. | BitVM chunk/wrap_hasher.rs directly invokes BLAKE3 for64/128/192/448byte field/accumulator commitments. The source truncates to16bytes; our32byte output is the complete standard prefix, not a full BitVM verifier. |
| `crypto-shake256-xof` | SHAKE256,0–511bytes→250bytes; rate136/domain1f, up to4absorbs+2squeezes | All6complete supported official NIST2000bit outputs;8derived rate/input boundaries;3length/canonical-padding/output negatives. All1619SHAKE256 source cases inventoried. | FIPS204 ML-DSA invokes SHAKE256; this is a PQ-authorization dependency, not evidence of deployed Bitcoin ML-DSA or a full signature verifier. No extra Keccak-permutation group. |
| `crypto-ml-dsa-ntt256` | FIPS204 degree256 NTT+inverse; q8380417,zeta1753,all8stages and inverse scale8347681 | 6full polynomials in each direction checked against independent directDFT/inverse;3range/output/direction negatives. No official isolated NTT outputKAT found. | ML-DSA uses the complete transform for lattice signature arithmetic. This is a credible future Bitcoin PQ-verifier dependency; no claim of a current Bitcoin deployment or full ML-DSA verifier. |
| `crypto-poseidon2-koalabear16` | KoalaBear q2130706433,width16,cubic S-box,8full+20partial rounds; two exact constant profiles | Complete published Plonky3default16field KAT;10derived profile/boundary cases;3canonical-input/profile/output negatives. Exact Ziren profile outputs are derived, not an upstream KAT. | GOAT bitvm-gc default verifiable-circuit feature selects_poseidon2; Cargo.lock pins ProjectZKM/poseidon2→Ziren, whose exact constants are checked. This is a full permutation component, not a full garbled bridge verifier. |
| `app-webauthn-counter-wallet` | Enrolled ES256 WebAuthn withdrawal; actual sig_all_hash challenge, RP/origin/UP+UV, canonical DER, monotone32bit counter and same-leaf native continuation | 3positive native state transitions;14signed policy/canonical encoding/dataflow/state/value/transaction negatives. Integer P256 reference control matches RFC6979. | W3C WebAuthn Level2 authentication relation is adapted into native Bitcoin wallet authorization; enrollment/attestation/TLS are external. Counter-capable authenticators only; fixed37byte authenticatorData and bounded published clientData-prefix verification. |

The byte-oriented NIST ZIP contains8files. SHAKE256ShortMsg/LongMsg/VariableOut supply1619cases; exactly6have a complete2000bit output within the511byte input bound. SHAKE128, Monte Carlo, other output sizes and longer inputs remain explicitly outside this profile. This is not CAVP validation. BLAKE3 keyed/derive-key modes and longer inputs are inventoried but not claimed. See the complete machine-readable inventories in `vendor-specs/crypto-families/`.

The Poseidon2 profiles are one family. The primary authors' BN254 example was acquired during source discovery but is not substituted for the inventoried Bitcoin-project KoalaBear profile. Plonky3v0.5.1 gives the complete published KAT; GitHub tag-resolution API access returned403, so the tag and SHA256 byte pins are preserved without inventing a commit. GOAT/Ziren profile outputs are independently derived from the exact pinned constants; its guest test has no published output assertion. No current mainnet adoption is inferred from repository use.

## Reproduction and execution paths

The Haskell compiler is GHC9.8.4 from the local Nix package environment. Direct builds use `-O1 -threaded -rtsopts -isrc`, the local `dist-newstyle/packagedb/ghc-9.8.4`, exact `-package-id Simplicity-0.0.0-inplace-Simplicity-Core`, `-package Simplicity -package jet-discovery`. NTT has compilation-only simplifier flags recorded in its source. The runner records the binary hash, complete local source closure, runtime KAT bytes, actual executable exit status and log hashes. Its own source is copied into each new freeze.

The current-source check above follows the selected program's local imports, rather than unrelated modules also linked by the multi-family driver. The complete original driver/source closure remains frozen. Tx.hs changed only in the unused parseRawTx function after the first WebAuthn/Poseidon2 build: a raw outpoint-byte reversal was removed. These entries exclusively use unchanged dummyOutpoint/mkInput/mkOutput/mkTx/mkEnv/defaultTap builders. The exact two-source diff and parent's codec audit confirm that this parser-only correction does not affect their fixtures. No other source difference is silently accepted.

Run the corresponding local driver binary with `tools/run_crypto_validation.py --label FRESH-LABEL --binary BINARY --build-dir BUILD-DIR --driver tools/CryptoFamilyVectors.hs --heap 16 --group blake3 --group shake --group ntt`. Every label is immutable; existing evidence is never overwritten. WebAuthn uses `tools/WebAuthnProbe.hs`, `--heap32 --group full`. Poseidon2 uses `--group poseidon2`. These commands validate the complete programs and actual same-CMR mutations.

Poseidon2 and WebAuthn use the prepared bound-program API: one aggregate witness followed by a pure witness-free kernel. Drivers assert canonical composition CMR equality and prepared-path observability. The three streamed component frontends deliberately use ordinary execution because independent block/output witnesses enter only at their consuming stages. Shared headers/inputs enter once and flow through projections. No equality between repeated witness occurrences is assumed.

## Retained failures and separate reference evidence

The earlier whole-array BLAKE3/SHAKE/NTT build each hit the16GiB cap during initial graph construction, before a vector result: actual exits251 and full frozen sources/logs remain under `reports/data/crypto-family-full-*` and the respective verification files. Their partial/compression/reference results never confer complete-program credit. Earlier4GiB Poseidon2 construction failures are likewise retained; the later complete14vector pass uses its recorded optimized build.

Independent reference audit: `reports/data/crypto-family-reference.txt` and `crypto-family-reference-status.json` (actual exit0). All19supported BLAKE3 KATs,6complete SHAKE KATs, all6ML-DSA polynomials against independent FIPS butterflies, and the published Poseidon2 KAT are checked. WebAuthn reference and22native hash/DER boundary helper checks are separate in `webauthn-reference.txt`, `webauthn-hashes.txt`, and `webauthn-helper-status.json`. They do not replace the full17wallet vectors.

## Provenance and licensing

Every acquired spec/source is inert data under `vendor-specs/crypto-families/` or the earlier `crypto-growth/` packet. No downloaded code is executed. URLs, revisions, licenses/access gaps and SHA256 hashes appear in the adjacent manifests; test extraction scripts parse numeric data without evaluating source code. All source rows, including discovery-only BN254 materials and source-access gaps, remain inventoried.
