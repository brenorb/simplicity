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
import Simplicity.Ty.Word (word128, word256)
import Simplicity.Weight (Weight)

import JetDiscovery.JetSets (Candidate(..), SomeCandidate(..))
import JetDiscovery.Lib.Kernels (sha256Pair, wotsChain)
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark

data CandidateInfo = CandidateInfo
  { ciName :: String
  , ciCost :: Weight
  , ciMethod :: String
  }

-- | (name, ESTIMATE cost, how the estimate was made)
candidateInfo :: [CandidateInfo]
candidateInfo =
  [ CandidateInfo "m31_mul" (2 * cost "FullMultiply32") "2 x FullMultiply32: one 32x32 multiply plus a Mersenne fold of similar cost"
  , CandidateInfo "qm31_mul" (cost "FeMultiply") "FeMultiply: 16 small-limb products and reductions, comparable to a 10x26-bit-limb secp256k1 field multiply"
  , CandidateInfo "keccak_f1600" (2 * cost "Sha256Block") "2 x Sha256Block: software Keccak-f[1600] takes roughly twice a SHA-256 compression"
  , CandidateInfo "blake2s_compress" (cost "Sha256Block") "Sha256Block: BLAKE2s compression and SHA-256 compression cost about the same in software"
  , CandidateInfo "blake2b_compress" (1.5 * cost "Sha256Block") "1.5 x Sha256Block: BLAKE2b compresses 128 bytes with 64-bit words"
  , CandidateInfo "sha256_wots_chain_16" (15 * cost "Sha256Block") "15 x Sha256Block: a Winternitz chain is at most 15 compressions (the jet is priced at its worst case)"
  , CandidateInfo "sha256_pair" (2 * cost "Sha256Block") "2 x Sha256Block: SHA-256 of 64 bytes is two compressions"
  , CandidateInfo "pubkey_unpack_neg" (cost "FeNormalize") "FeNormalize: a range check and a negation on one field element"
  , CandidateInfo "signature_unpack" (cost "FeNormalize" + cost "ScalarNormalize") "FeNormalize + ScalarNormalize: range checks on r and s"
  , CandidateInfo "div_mod_256" (4 * cost "DivMod128_64") "4 x DivMod128_64: schoolbook 256-bit division by 64-bit limbs"
  , CandidateInfo "multiply_128" (4 * cost "Multiply64") "4 x Multiply64: four 64x64 products"
  ]

costOf :: String -> Weight
costOf n = head ([ ciCost c | c <- candidateInfo, ciName c == n ] ++ [error ("no candidate " ++ n)])

candidates :: [SomeCandidate]
candidates =
  [ SomeCandidate (Candidate "m31_mul" (costOf "m31_mul") Stark.m31Mul)
  , SomeCandidate (Candidate "qm31_mul" (costOf "qm31_mul") Stark.qm31Mul)
  , SomeCandidate (Candidate "keccak_f1600" (costOf "keccak_f1600") Hashes.keccakF)
  , SomeCandidate (Candidate "blake2s_compress" (costOf "blake2s_compress") (Hashes.blake2F Hashes.blake2s))
  , SomeCandidate (Candidate "blake2b_compress" (costOf "blake2b_compress") (Hashes.blake2F Hashes.blake2b))
  , SomeCandidate (Candidate "sha256_wots_chain_16" (costOf "sha256_wots_chain_16") wotsChain)
  , SomeCandidate (Candidate "sha256_pair" (costOf "sha256_pair") sha256Pair)
  , SomeCandidate (Candidate "pubkey_unpack_neg" (costOf "pubkey_unpack_neg") Secp.pubkey_unpack_neg)
  , SomeCandidate (Candidate "signature_unpack" (costOf "signature_unpack") Secp.signature_unpack)
  , SomeCandidate (Candidate "div_mod_256" (costOf "div_mod_256") (Arith.div_mod word256))
  , SomeCandidate (Candidate "multiply_128" (costOf "multiply_128") (Arith.multiply word128))
  ]
