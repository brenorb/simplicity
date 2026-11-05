# Scoped witness data-flow audit

A Simplicity `witness` node does not commit to its value in the CMR. Repeating
`witness v` in Haskell, even through a shared variable or helper, does not
require all serialized occurrences to hold equal values. Honest vectors can
therefore pass while a malicious spender supplies different values to a check
and its later use. `tools/WitnessAliasing.hs` preserves the independent
reproducer from the BIP audit. This is a corpus-construction bug; no existing
consensus code or jet specification is changed.

The repairs bind every multiply-used logical header or proof tuple once and
route repeated fields through `iden`, `take` and `drop`. Independently consumed
chain/path words enter once at their unique stage and then flow as data. Hashing
state retains the bound header. Repeated use of a projection copies data rather
than introducing another unconstrained witness. Carrying every proof word through
every hash was tested first, exhausted the 8 GiB diagnostic heap, and was replaced
by this smaller binding-preserving state layout.

| Program | Repeated fields before repair | Binding after repair | Adversarial vector coverage |
| --- | --- | --- | --- |
| `eprint-blind-schnorr-response` | key, nonce point, response, alpha/beta and blinded challenge | one `BlindW` witness; pure `blindResponseT` | different valid key, alpha, challenge, response, beta+n; changed fields retain CMR and reject |
| `eprint-frost-signature-share` | D/E/Y points, rho, challenge, lambda and response | one `FrostW` witness; pure `frostShareT` | different public share, hiding commitment, response and binding factor; rho+n rejects |
| `eprint-adaptor-sig` | public key/message, R-prime, T and response | one adaptor tuple; pure verifier | changed message/adaptor point, unchanged CMR |
| `eprint-musig2-keyagg` | compressed key prefixes/x coordinates in validity/hash/aggregation paths | one3-key tuple plus expected aggregate | upstream malformed keys, order mismatch and valid cases at one CMR |
| `eprint-ring-sig` | ring keys, message, initial challenge and responses | one fixed4-key/4-response tuple; current challenge threaded with bound input | changed message at same CMR |
| `eprint-dleq-cashu` | A/B/C, challenge and response between curve checks and equations/hash | one DLEQ tuple | C from another secret at same CMR; this remains the documented custom transcript, not exact NUT12 |
| `pq-lms-sha256-m32-h10` | q and randomizer reused across digest/chains/tree; proof subterms could recur | one q/R header; each chain/path word enters once; q carried as data through chains and Merkle pipeline | corrupted chain/path, q in/out of range, randomizer splice; official RFC8554 KAT adds q3→4 and C→0 splices |
| `pq-xmss-sha2-10-256` | index/randomizer/address fields and repeated proof subterms | one index/R header; each chain enters once and each sibling is paired into stage data before left/right use | chain/path corruption, index17→18, invalid index1024 and randomizer splice |
| `pq-shrincs-stateful` | seed, roots, R, height/index/counter across digest, WOTS and Merkle checks | one header tuple;32chain/8auth words each consumed once | seed/R/counter/path/chain splices, inconsistent depth/index and changed transaction |
| `pq-shrincs-stateless` | seed/roots/R across FORS, hypertree and final root comparison | one header tuple;360independent proof words each enter once; all stages carry the bound header | seed/R/claimed-root, FORS preimage and top-layer chain splices; changed transaction |

All repaired programs have new Simplicity layouts/CMRs and potentially different
combinator/copy costs. RFC/protocol byte strings and equations are preserved.
Previous WU reports must be regenerated; prior passing vectors do not validate
the old aliasing construction. The earlier `lms-kat-memory.txt` records the
pre-binding optimization and is not a validation log for the final binding fix.
`*-whole-proof-heap-failure.txt` and `xmss-whole-proof-interrupted.txt` preserve
failed/stopped construction diagnostics, not passing verification results.

The BN254 field/Fp2 wrappers already bind their complete operand/result tuples
once. BitVM NAND and equivocation wrappers already bind their complete tuples
once. Lamport uses each independent signature preimage in one hash check, with
the message obtained deterministically from the transaction; it does not
reintroduce a multiply-used logical witness. These five entries needed no
binding change.

`tools/WitnessBoundVerification.hs` runs vectors sequentially without cost
analysis, using `Run.runVector`: success requires both the expected result and
an identical program CMR for every changed witness. Run its groups after the
current library build (`eprint`, `eprint-original`, `lms-kat`, `lms`, `xmss`,
`shrincs-stateful`, `shrincs-stateless`, `bn254`). Logs under `reports/data/`
state actual outcomes; pending groups must not be represented as validated.
This is a scoped audit of the assigned modules, not a claim that the entire
corpus has completed its broader data-flow audit.

## Canonical encodings

The existing secp256k1 arithmetic accepts field/scalar inputs modulo the curve
moduli. A verifier must separately enforce the scheme's serialized encoding
ranges. The old adaptor, ring and DLEQ wrappers omitted these bounds. Six
independent arithmetic fixtures confirmed real false acceptance: adaptor
response `1+n`, adaptor public key `p+1`, DLEQ `B.x=p+1`, DLEQ `C.x=p+1`, a
non-signing ring key `p+1`, and a ring response `1+n`. Each has a valid canonical
control, and changing its encoding preserves the CMR. The malformed adaptor/C
fixtures recompute the challenge using the actual raw bytes; they do not depend
on accidentally hashing a normalized encoding.

The repaired verifiers require all external affine coordinates and x-only keys
to be `<p`, and all externally supplied signature scalars to be `<n`. Internal
Fiat-Shamir challenges still reduce hashes modulo `n`, as the documented local
relations require. MuSig2 already checks compressed prefixes and `x<p` and
needed no extra encoding guard. The DLEQ entry remains the explicitly documented
64-byte-affine custom transcript; it is not an interoperable NUT-12 decoder.

`Corpus.Eprint.encodingProbes` exports the six control/attack pairs, and
`tools/EprintCanonicalProbe.hs` checks equal CMR, control acceptance and malformed
rejection. `reports/data/eprint-canonical-before.txt` preserves all six old
false accepts (actual executable exit status 0). The after-run and its separate
status JSON are the current repair evidence. All six after-probes completed:
canonical controls accepted, malformed encodings rejected, equal CMR in every
pair, actual executable exit status 0 (224.704 seconds). An unfinished verifier
group is not a pass.

## Construction diagnostics

The compact LMS binding passed both the four-vector official RFC8554 certificate
fixture and all seven transaction-signature vectors under the 8 GiB cap. The
compact stateful SHRINCS binding passed all twelve vectors under the same cap.
Actual statuses and timings are in `data/witness-bound-status.json` and the
corresponding logs. XMSS's first compact implementation still exhausted the
cap; its subsequent F/H kernels use direct fixed-width SHA-256 blocks shared
after substitution of existing jets. Kernel bytes are checked against the
independent reference by `tools/XmssKernelProbe.hs`; the later XMSS verification
run has its own `xmss-kernel-witness-bound-status.json`. No cost or memory failure
is counted as a successful verifier run.

| Completed group | Vectors | Actual exit status | Elapsed seconds | Maximum heap residency bytes |
| --- | ---: | ---: | ---: | ---: |
| Eprint expansion before final identity-case correction | 23 | 0 | 193.765 | 999652856 |
| Current FROST relation including identity cases | 8 | 0 | 111.249 | 642894928 |
| LMS official RFC8554 certificate | 4 | 0 | 115.380 | 3688231288 |
| LMS transaction verifier | 7 | 0 | 249.408 | 6288291928 |
| Stateful SHRINCS | 12 | 0 | 224.845 | 1737795224 |
| Final shared XMSS transaction verifier | 7 | 0 | 288.886 | 3961502344 |
| Direct-kernel stateless SHRINCS (16 GiB cap) | 7 | 0 | 1145.480 | 15273293304 |
| Standard FIPS205 official case266 and corruptions (24 GiB cap) | 4 | 0 | 802.738 | 9133865632 |

The original eprint 14-vector data-flow-only run also passed before the extra
encoding guards; the six completed canonical controls/regressions test those
subsequent guards. Full current corpus validation is owned by the shared runner.
The final XMSS layout additionally binds its derived message digest/checksum
once and shares an entire fixed-type WOTS chain. Stateless SHRINCS similarly
shares its fixed-type existing-jet WOTS expression. Their capped sequential
run is recorded separately in `data/hashsig-shared-witness-bound-status.json`;
earlier 8 GiB failures remain in the prior logs and are not overwritten.

The shared-context stateless construction also exhausted 16 GiB. Early
substitution of the individual SHA context helpers did not improve it; that
boilerplate was removed and its unsuccessful diagnostic remains recorded.
The final stateless frontend instead uses the pure
`Lib.ShrincsHash.chainRef`: a seeded compression state, exact 18-byte address
prefix, start nibble and node. Its 38-byte suffix fits one fixed SHA-256 block
after padding. It introduces no witnesses, preserves the draft's hash bytes,
and changes expression/CMR/cost shape. The fixed and generic chain frontends
are one candidate primitive family, not additional applications.

All 36 direct-kernel/wrapper byte-reference cases passed (actual exit 0,
15.222 seconds, maximum residency 309097792 bytes). Separately, all 18
`Ref.ShrincsHash.seededCases` passed against full-message hashing in
`Ref.Shrincs.tweak`. The updated full stateless run is recorded in
`data/shrincs-stateless-direct-witness-bound-status.json` and its log; the
complete group passed: valid reference signature accepted and all six negative
vectors rejected, with unchanged CMR (actual exit0,1145.480 seconds). Prior heap failures are construction
limits, not observed semantic verifier failures.

The final group review also found an FROST completeness edge case independent
of witness aliasing. RFC9591 `verify_signature_share` compares group elements
and permits an identity intermediate commitment share. The old affine
normalization rejected `D=G,E=-G,rho=1,Y=5G,c=7,lambda=3,z=105`, although the
share equation holds. The repaired relation compares Jacobian elements with
`gej_equiv`, retaining canonical external point/scalar guards and one bound
input. Two entry vectors preserve the valid identity case and a wrong response.
The actual before probe records `(sameCMR=True,validAccepted=False,badAccepted=False)`;
after-probe accepted the valid case and rejected the wrong response at the
same CMR (exit 0, 36.854 seconds). All eight current FROST vectors passed
(exit 0, 111.249 seconds); `data/frost-identity-repair-status.json` and the
associated logs preserve both results. The expansion now has 25 vectors:
the other 17 previously passing vectors are unchanged.
