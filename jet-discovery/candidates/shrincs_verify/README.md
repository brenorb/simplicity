# Candidate: `shrincs_verify` — monolithic SHRINCS signature verification

**Corpus evidence withdrawn pending the fresh complete run.** Numerical corpus examples below describe historical expressions and cannot be attributed to the repaired registry. Candidate prices remain explicitly ESTIMATE. Current vector evidence is in [CURRENT-VALIDATION.md](../../reports/CURRENT-VALIDATION.md); no old ranking is current.

## Type signature
`((Word384 pubkey, Word256 msg), signature) -> ()`, with the signature as a bounded buffer
(stateful: 548 to 4619 bytes; stateless: 5777 bytes).

## Specification
`shrincs_verify` of the SHRINCS draft (vendor-specs/shrincs/SHRINCS.md). The stateful branch is implemented and
tested in Simplicity as `pq-shrincs-stateful` (leaf depth <= 8) and transcribed in `src/JetDiscovery/Ref/Shrincs.hs`;
the stateless branch as `pq-shrincs-stateless`, with its reference in `src/JetDiscovery/Ref/SlhDsa.hs`.

## Cost (ESTIMATE)
SHRINCS's own compression counts (SHRINCS.md, Performance) times `Sha256Block` (0.765 WU):
- stateful, up to 509 compressions: 389.5 WU;
- stateless (SLH-DSA path), up to 2792 compressions: 2,136.1 WU.
A jet would be priced at its worst case.

## Corpus evidence
- `pq-shrincs-stateful`: 8,039.435 WU measured for depth <= 8 (reports/corpus-results.md), of which 89.7% is the
  32 WOTS+C chains. With the `sha256_wots_chain_16` candidate: 1,199.307 WU (ESTIMATE). A monolithic jet: about
  390 WU, a further 3x.
- The static bound counts 480 chain steps; the constant-sum rule makes verification do exactly 240. Only a jet that
  validates the constant sum first could be priced at the real 240 steps; the chain jet must assume 15 per chain.
- Under the ASSUMPTION budget (witness bytes + 50), the measured program needs 4,366 WU of padding; the measured
  program with the chain jet already fits (1,199 WU against 3,673 WU); a monolithic jet would too.
- `pq-shrincs-stateless` (FORS k=10, a=13; hypertree d=5, h'=9): 58,344.501 WU measured; with the chain candidate
  20,937.551 WU (2.8×, ESTIMATE), which fits the ASSUMPTION budget (23,648 WU for a 5,520-byte signature). A
  monolithic jet: about 2,136 WU, a further 10x; most of that gap is tweakable-hash plumbing that a `sha256_thash`
  jet would also remove.

## Generality
Single scheme (draft BIP). SHRINCS's stateless path is FIPS 205 compatible (SLH-DSA-SHA2 with its own parameter
set), so a `slh_dsa_sha2_verify` jet parameterised by the parameter set would serve NIST SLH-DSA as well.

## Verification burden
High: a large specification (WOTS+C, FXMSS, FORS, hypertree), although every hash is the already proven SHA-256
compression. The chain jet plus a tweakable-hash jet give most of the saving at a fraction of the proof work.

## Alternatives considered
`sha256_wots_chain_16` (+ a single tweakable-hash jet for H and FORS leaves): 6.7x (stateful) and 2.8x (stateless) now, general across hash-based
schemes, much smaller proof. Recommended first.
