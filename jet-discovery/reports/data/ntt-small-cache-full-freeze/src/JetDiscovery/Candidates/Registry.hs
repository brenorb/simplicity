-- | The registry of candidate jets used by the what-if cost overlay
-- ("JetDiscovery.WhatIf").  Each candidate's specification is an existing
-- corpus kernel, so the overlay replaces every occurrence of that kernel.
--
-- Every cost here is an ESTIMATE: there is no C implementation or benchmark.
-- Each is scaled from the benchmarked cost of the closest existing jet
-- (Simplicity.Bitcoin.Benchmarks.cost), as stated next to it and in
-- candidates/<name>/README.md.
module JetDiscovery.Candidates.Registry
  ( candidates
  , CandidateInfo(..)
  , candidateInfo
  ) where

import Prelude hiding (drop, take)

import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Benchmarks (cost)
import Simplicity.Ty.Word (word128, word256, word512)
import Simplicity.Weight (Weight)

import JetDiscovery.JetSets (Candidate(..), SomeCandidate(..))
import JetDiscovery.Lib.Kernels (sha256Pair, wotsChain)
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark
import qualified JetDiscovery.Lib.Ripemd160 as Ripemd
import qualified JetDiscovery.Corpus.Ed25519 as Ed25519
import qualified JetDiscovery.Corpus.P256 as P256
import qualified JetDiscovery.Corpus.BN254 as BN254
import qualified JetDiscovery.Corpus.ContractExpansion as Contract
import qualified JetDiscovery.Lib.ShrincsHash as ShrincsHash

data CandidateInfo = CandidateInfo
  { ciName :: String
  , ciCost :: Weight
  , ciMethod :: String
  }

-- | (name, ESTIMATE cost, how the estimate was made)
candidateInfo :: [CandidateInfo]
candidateInfo =
  [ CandidateInfo "bn254_fp_multiply" (2 * cost "FeMultiply") "ESTIMATE: 2 x FeMultiply for a generic 254-bit Montgomery reduction; requires an implementation and benchmark"
  , CandidateInfo "secp256k1_ecdsa_verify" (sum (map cost ["ScalarInvert","LinearCombination1","GejNormalize","GeIsOnCurve","ScalarNormalize"])) "ESTIMATE: sum of existing ScalarInvert, LinearCombination1, GejNormalize, GeIsOnCurve and ScalarNormalize benchmarks"
  , CandidateInfo "ecrecover" (sum (map cost ["ScalarInvert","Decompress","LinearCombination1","GejNormalize","ScalarNegate"]) + 2 * cost "ScalarMultiply" + 2 * cost "Sha256Block") "ESTIMATE: existing secp256k1 operation benchmarks plus Keccak priced as 2 x Sha256Block"
  , CandidateInfo "m31_mul" (2 * cost "FullMultiply32") "2 x FullMultiply32: one 32x32 multiply plus a Mersenne fold of similar cost"
  , CandidateInfo "qm31_mul" (cost "FeMultiply") "FeMultiply: 16 small-limb products and reductions, comparable to a 10x26-bit-limb secp256k1 field multiply"
  , CandidateInfo "keccak_f1600" (2 * cost "Sha256Block") "2 x Sha256Block: software Keccak-f[1600] takes roughly twice a SHA-256 compression"
  , CandidateInfo "blake2s_compress" (cost "Sha256Block") "Sha256Block: BLAKE2s compression and SHA-256 compression cost about the same in software"
  , CandidateInfo "blake2b_compress" (1.5 * cost "Sha256Block") "1.5 x Sha256Block: BLAKE2b compresses 128 bytes with 64-bit words"
  , CandidateInfo "sha256_wots_chain_16" (15 * cost "Sha256Block") "15 x Sha256Block: a Winternitz chain is at most 15 compressions (the jet is priced at its worst case)"
  , CandidateInfo "sha256_wots_chain_16_fixed" (15 * cost "Sha256Block") "ESTIMATE: 15 x Sha256Block for the fixed 18-byte-address n16 chain frontend; same primitive family as sha256_wots_chain_16"
  , CandidateInfo "sha256_pair" (2 * cost "Sha256Block") "2 x Sha256Block: SHA-256 of 64 bytes is two compressions"
  , CandidateInfo "pubkey_unpack_neg" (cost "FeNormalize") "FeNormalize: a range check and a negation on one field element"
  , CandidateInfo "signature_unpack" (cost "FeNormalize" + cost "ScalarNormalize") "FeNormalize + ScalarNormalize: range checks on r and s"
  , CandidateInfo "div_mod_256" (4 * cost "DivMod128_64") "4 x DivMod128_64: schoolbook 256-bit division by 64-bit limbs"
  , CandidateInfo "multiply_128" (4 * cost "Multiply64") "4 x Multiply64: four 64x64 products"
  , CandidateInfo "multiply_256" (16 * cost "Multiply64") "16 x Multiply64: sixteen 64x64 products (schoolbook 256x256)"
  , CandidateInfo "div_mod_512" (16 * cost "DivMod128_64") "16 x DivMod128_64: schoolbook 512-by-256-bit division with 64-bit limbs (4x div_mod_256's estimate)"
  , CandidateInfo "ripemd160_compress" (cost "Sha256Block") "Sha256Block: RIPEMD-160 and SHA-256 compression cost about the same in software"
  , CandidateInfo "sha512_compress" (1.5 * cost "Sha256Block") "1.5 x Sha256Block: SHA-512 compresses 128 bytes with 64-bit words (as blake2b_compress)"
  , CandidateInfo "p256_fe_multiply" (1.5 * cost "FeMultiply") "1.5 x FeMultiply: a P-256 field multiply with Solinas reduction is somewhat slower than libsecp256k1's"
  , CandidateInfo "ed25519_fe_multiply" (cost "FeMultiply") "FeMultiply: 2^255-19 reduction is as cheap as secp256k1's (fold by 38)"
  ]

costOf :: String -> Weight
costOf n = head ([ ciCost c | c <- candidateInfo, ciName c == n ] ++ [error ("no candidate " ++ n)])

candidates :: [SomeCandidate]
candidates =
  [ SomeCandidate (Candidate "bn254_fp_multiply" (costOf "bn254_fp_multiply") BN254.fpMul)
  , SomeCandidate (Candidate "secp256k1_ecdsa_verify" (costOf "secp256k1_ecdsa_verify") Contract.ecdsaVerify)
  , SomeCandidate (Candidate "ecrecover" (costOf "ecrecover") Contract.ecRecover)
  , SomeCandidate (Candidate "m31_mul" (costOf "m31_mul") Stark.m31Mul)
  , SomeCandidate (Candidate "qm31_mul" (costOf "qm31_mul") Stark.qm31Mul)
  , SomeCandidate (Candidate "keccak_f1600" (costOf "keccak_f1600") Hashes.keccakF)
  , SomeCandidate (Candidate "blake2s_compress" (costOf "blake2s_compress") (Hashes.blake2F Hashes.blake2s))
  , SomeCandidate (Candidate "blake2b_compress" (costOf "blake2b_compress") (Hashes.blake2F Hashes.blake2b))
  , SomeCandidate (Candidate "sha256_wots_chain_16" (costOf "sha256_wots_chain_16") wotsChain)
  , SomeCandidate (Candidate "sha256_wots_chain_16_fixed" (costOf "sha256_wots_chain_16_fixed") ShrincsHash.chainRef)
  , SomeCandidate (Candidate "sha256_pair" (costOf "sha256_pair") sha256Pair)
  , SomeCandidate (Candidate "pubkey_unpack_neg" (costOf "pubkey_unpack_neg") Secp.pubkey_unpack_neg)
  , SomeCandidate (Candidate "signature_unpack" (costOf "signature_unpack") Secp.signature_unpack)
  , SomeCandidate (Candidate "div_mod_256" (costOf "div_mod_256") (Arith.div_mod word256))
  , SomeCandidate (Candidate "multiply_128" (costOf "multiply_128") (Arith.multiply word128))
  , SomeCandidate (Candidate "multiply_256" (costOf "multiply_256") (Arith.multiply word256))
  , SomeCandidate (Candidate "div_mod_512" (costOf "div_mod_512") (Arith.div_mod word512))
  , SomeCandidate (Candidate "ripemd160_compress" (costOf "ripemd160_compress") Ripemd.ripemd160Compress)
  , SomeCandidate (Candidate "sha512_compress" (costOf "sha512_compress") Ed25519.sha512Compress)
  , SomeCandidate (Candidate "p256_fe_multiply" (costOf "p256_fe_multiply") P256.mulmod)
  , SomeCandidate (Candidate "ed25519_fe_multiply" (costOf "ed25519_fe_multiply") Ed25519.mulmod)
  ]
