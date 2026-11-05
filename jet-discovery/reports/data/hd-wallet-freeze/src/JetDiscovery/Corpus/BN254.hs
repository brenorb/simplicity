{-# LANGUAGE ScopedTypeVariables #-}
-- | BN254 arithmetic for pairing-based Bitcoin bridge verifiers. No pairing
-- check is claimed: these independently tested kernels measure the base-field
-- bottleneck and supply the units for an explicitly labelled extrapolation.
module JetDiscovery.Corpus.BN254
  ( entries, pBN254, fpAdd, fpSub, fpMul, fp2Mul, fp2MulRef ) where

import Prelude hiding (drop, take, not, and, or, subtract)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

-- EIP-196/197 alt_bn128 base field, NOT the scalar-field order.
pBN254 :: Integer
pBN254 = 21888242871839275222246405745257275088696311157297823662689037894645226208583

type Fp2 = (Word256, Word256)

kw :: (Core term, TyC a) => Integer -> term a Word256
kw = konst . toWord256

-- Canonical input check; used in corpus wrappers, not built into every field op.
canonical :: Assert term => term Word256 ()
canonical = (iden &&& kw pBN254) >>> Arith.lt word256 >>> verify

-- Since p < 2^254, a+b fits 256 bits for canonical inputs.
fpAdd :: Assert term => term (Word256, Word256) Word256
fpAdd = Arith.add word256 >>> ih >>> (iden &&& (iden &&& kw pBN254 >>> Arith.subtract word256))
        >>> (ioh &&& (oh &&& iih)) >>> cond oh ih

fpSub :: Assert term => term (Word256, Word256) Word256
fpSub = Arith.subtract word256 >>> cond (iden &&& kw pBN254 >>> Arith.add word256 >>> ih) iden

-- Deliberately plain Integer-style reduction. This forces the expensive work
-- instead of substituting a secp256k1 field jet with the wrong modulus.
fpMul :: Assert term => term (Word256, Word256) Word256
fpMul = (Arith.multiply word256 &&& (kw 0 &&& kw pBN254)) >>> Arith.div_mod word512 >>> ih >>> ih

-- Fp2 = Fp[u]/(u^2+1); Karatsuba: 3 fpMul plus additions.
fp2Mul :: Assert term => term (Fp2, Fp2) Fp2
fp2Mul = s1 >>> s2 >>> out
 where
  s1 = iden &&& ((ooh &&& ioh >>> fpMul) &&& (oih &&& iih >>> fpMul))
  -- s1: (input, (ac,bd)); push (a+b)(c+d)
  s2 = iden &&& (((take ooh &&& take oih >>> fpAdd) &&& (take ioh &&& take iih >>> fpAdd)) >>> fpMul)
  ac = take (drop oh)
  bd = take (drop ih)
  out = ((ac &&& bd) >>> fpSub) &&& ((((ih &&& ac) >>> fpSub) &&& bd) >>> fpSub)

fp2MulRef :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer)
fp2MulRef (a,b) (c,d) = ((a*c-b*d) `mod` pBN254, (a*d+b*c) `mod` pBN254)

entries :: [Entry]
entries = [base, extension]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  base = Entry
    { entryId = "eprint-bn254-fp-multiply"
    , entryTitle = "BN254 base-field multiply and exact modular reduction"
    , entrySpec = "EIP-196/197 base field; eprint 2024/1498 Practical Implementation of Pairing-Based Cryptography in Bitcoin"
    , entryCategory = Eprint
    , entryVectorSource = Derived "Haskell Integer multiplication modulo EIP-196 base-field prime; boundary/carry cases"
    , entryAssumptions = ["canonical 256-bit operands checked", "generic 512-bit div/mod; no pairing check or security claim", "Bitcoin path: Groth16 bridge/dispute verification (BitVM)"]
    , entryProgram = \((a,b),c) -> Prog $ witness ((toWord256 a,toWord256 b),toWord256 c) >>> ((take oh >>> canonical) &&& (take ih >>> canonical) &&& ((take fpMul &&& ih) >>> eq >>> verify)) >>> unit
    , entryVectors = [Vector (show (a,b)) env ((a,b),a*b `mod` pBN254) Accept | (a,b) <- [(0,0),(1,pBN254-1),(pBN254-1,pBN254-1),(2^253,2^253),(1234567890123456789,9876543210987654321)]] ++
                     [Vector "incorrect reduction" env ((pBN254-1,pBN254-1),2) Reject, Vector "noncanonical operand" env ((pBN254,1),0) Reject]
    }
  extension = Entry
    { entryId = "eprint-bn254-fp2-multiply"
    , entryTitle = "BN254 quadratic extension multiplication (u^2 = -1)"
    , entrySpec = "EIP-197 Fp2; eprint 2024/1498 pairing arithmetic"
    , entryCategory = Eprint
    , entryVectorSource = Derived "Haskell Integer polynomial multiplication/reduction, independent of Simplicity Karatsuba form"
    , entryAssumptions = ["all four base-field coefficients canonical and checked", "three fp multiplications plus fp additions/subtractions", "kernel for G2/Miller arithmetic, not a Groth16 verifier"]
    , entryProgram = \((a,b),c) -> Prog $ witness ((toFp2 a,toFp2 b),toFp2 c) >>>
        (((take (take oh) >>> canonical) &&& (take (take ih) >>> canonical)) &&& ((take (drop oh) >>> canonical) &&& (take (drop ih) >>> canonical)) &&& ((take fp2Mul &&& ih) >>> eq >>> verify)) >>> unit
    , entryVectors = [Vector (show (a,b)) env ((a,b),fp2MulRef a b) Accept | (a,b) <- [((1,0),(0,1)),((0,1),(0,1)),((pBN254-1,pBN254-1),(pBN254-1,pBN254-1)),((123,456),(789,101112))]] ++
                     [Vector "wrong real coefficient" env (((1,2),(3,4)),(pBN254-4,10)) Reject]
    }
  toFp2 (a,b) = (toWord256 a,toWord256 b)
