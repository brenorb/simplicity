{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Checks that each candidate jet's Simplicity specification (a corpus
-- kernel) agrees with an independent Haskell reference, and that the
-- BIP 340 reference signer reproduces the official test vectors.
module Main (main) where


import Control.Exception (bracket)
import Data.Maybe (isNothing)
import System.IO (openTempFile,hClose)
import System.Directory (getTemporaryDirectory,removeFile,removeDirectoryRecursive)
import JetDiscovery.Snapshot (saveResult,loadResult)
import Data.Bits (xor, (.&.), complement, rotateL, rotateR, shiftL, shiftR)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import Data.Word (Word32, Word64)
import qualified Data.List as L
import Test.Tasty (defaultMain, testGroup, TestTree)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)

import Simplicity.Term.Core ((>>>), (&&&), iden, unit, witness)
import qualified Simplicity.Term.Core as Core
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Bit (verify,cond)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Primitive (PrimEnv)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Term as Term
import Simplicity.Digest (hash0)
import qualified Simplicity.Ty.Word as W

import JetDiscovery.Lib.Bytes (konst, w8, w32, w64, w256FromBytes, w256ToBytes)
import JetDiscovery.Lib.Kernels (sha256Pair, wotsChain)
import qualified JetDiscovery.Corpus.Hashes as Hashes
import qualified JetDiscovery.Corpus.Stark as Stark
import qualified JetDiscovery.Ref.Bip340 as Bip340
import qualified JetDiscovery.Ref.Shrincs as Shrincs
import qualified JetDiscovery.Ref.ShrincsHash as ShrincsHashRef
import qualified JetDiscovery.Ref.SlhDsaStandard as StandardSlh
import qualified JetDiscovery.Lib.ShrincsHash as ShrincsHash
import qualified JetDiscovery.Corpus.P256 as P256
import qualified JetDiscovery.Corpus.Ripemd as Ripemd
import qualified JetDiscovery.Lib.Ripemd160 as Rmd
import qualified JetDiscovery.Corpus.Ed25519 as Ed
import qualified Data.ByteString.Char8 as BSC8
import qualified JetDiscovery.Regression.WitnessState as WitnessState
import qualified JetDiscovery.Corpus.Eprint as Eprint
import qualified JetDiscovery.Corpus.Lms as Lms
import JetDiscovery.Types (Prog(..), boundProgram, boundView, BoundView(..), boundEligible, Entry(..), Vector(..), Expect(..), Category(..), VectorSource(..))
import JetDiscovery.Run (progCmr, runVector, runVectors, vrOk, vrNote, measure, Measurement(..), runEntry, erMeasure)
import JetDiscovery.Profile (niCmr)
import JetDiscovery.Report (assumedWitnessStackBytes)
import JetDiscovery.Mine (mine,Group(..))
import JetDiscovery.Candidates.Impact (directIsolatedCost)
import JetDiscovery.Reprice (primitiveCost,restrictedCost)
import JetDiscovery.JetSets (PrimOnly, Ablate, NoSecpCurve, NoSecp, NoSha256)
import qualified Simplicity.Bitcoin.Dag as Dag
import JetDiscovery.WhatIf (WhatIf)
import JetDiscovery.Cost (TermWeight,milliWeigh)
import qualified JetDiscovery.Corpus.BN254 as BN
import qualified JetDiscovery.Corpus.ContractExpansion as Contract
import qualified JetDiscovery.Ref.Keccak as Keccak
import qualified JetDiscovery.Ref.FibonacciStark as FS
import qualified Data.Vector as V
import JetDiscovery.Tx

env :: PrimEnv
env = maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)

run :: Jets.FastEval Jets.JetType a b -> a -> Maybe b
run t = Jets.fastEval t env

-- deterministic pseudo-random integers (64-bit LCG)
rands :: Integer -> [Integer]
rands seed = tail (iterate (\x -> (x * 6364136223846793005 + 1442695040888963407) `mod` 2 ^ (64 :: Int)) seed)

main :: IO ()
main = defaultMain $ testGroup "jet-discovery"
  [ preparedTests
  , testGroup "full STARK reference"
      [ testCase "FFT matches direct polynomial evaluation" $ do
          let cs=V.fromList (map FS.base [3,5,7,11,13,17,19,23])
              evals=FS.lde 4 FS.coset cs
          V.toList evals @?= [FS.evaluatePoly cs (FS.mul FS.coset (FS.pow (FS.generator 4) j)) | j<-[0..15]]
      , testCase "generated AIR/DEEP/FRI proof and tampered proofs" $ do
          let p=FS.small; pr=FS.prove p
          assertBool "honest proof" (FS.verify p pr)
          assertBool "truncated proof" (not (FS.verify p (pr {FS.queries=[]})))
          assertBool "short root" (not (FS.verify p (pr {FS.traceRoot=BS.empty})))
          assertBool "integer narrowing prohibited" (not (FS.wireEncodable p (pr {FS.ood=((2^32,0),(0,0)):tail (FS.ood pr)})))
          assertBool "altered OOD" (not (FS.verify p (pr {FS.ood=FS.one:tail (FS.ood pr)})))
          assertBool "altered final constant" (not (FS.verify p (pr {FS.finalValue=FS.add FS.one (FS.finalValue pr)})))
      ]
  , testCase "same-CMR witness splitting is not logical aliasing" $ do
      let legacy x y=Prog (((witness (w8 x) &&& konst (w8 0)) >>> eq >>> verify) &&& ((witness (w8 y) &&& konst (w8 1)) >>> eq >>> verify) >>> unit)
          fixed x=Prog (witness (w8 x) >>> (((iden &&& konst (w8 0)) >>> eq >>> verify) &&& ((iden &&& konst (w8 1)) >>> eq >>> verify)) >>> unit)
          ev p=Jets.fastEval (Jets.unwrap (Jets.jetSubst (unProg p))) env ()
      progCmr (legacy 0 0) @?= progCmr (legacy 0 1)
      ev (legacy 0 0) @?= Nothing
      ev (legacy 0 1) @?= Just ()
      ev (fixed 0) @?= Nothing
      ev (fixed 1) @?= Nothing
  , testCase "published scalar and point encodings are canonical" $ do
      let ev p=Jets.fastEval (Jets.unwrap (Jets.jetSubst (unProg p))) env ()
      mapM_ (\(name,good,bad) -> do
        progCmr good @?= progCmr bad
        assertBool (name++" valid control") (ev good==Just ())
        assertBool (name++" noncanonical encoding") (ev bad==Nothing)) Eprint.encodingProbes
  , testCase "actual state update rejects witness-alias attack" $
      mapM_ (\(name,ok)->assertBool name ok) WitnessState.stateAliasChecks
  , testCase "Ed25519 SHA512 block padding is canonical" $ do
      let block n=BS.replicate 64 0<>BS.replicate n 7<>BS.singleton 128<>BS.replicate (47-n) 0<>BS.drop 16 (Bip340.bytesFromInt (512+8*toInteger n))
          value bs=W.toWord W.word1024 (Bip340.intFromBytes bs)
      mapM_ (\n->run Ed.sha512Padding (value (block n)) @?= Just ()) [0,1,15]
      run Ed.sha512Padding (value (BS.take 65 (block 0)<>BS.singleton 1<>BS.drop 66 (block 0))) @?= Nothing
      run Ed.sha512Padding (value (BS.take 112 (block 0)<>BS.drop 16 (Bip340.bytesFromInt 513))) @?= Nothing
  , testCase "profile CMR matches library commitment rules" $ do
      let program=Prog ((witness (w256FromBytes (BS.replicate 32 0)) &&& konst (w256FromBytes (BS.replicate 32 1))) >>> sha256Pair >>> unit)
          m=measure program
      niCmr (last (mProfile m)) @?= mCmr m
      mProfileTotal m @?= mCost m
      mCostWhatIf m @?= milliWeigh (Jets.unwrap (Dag.jetSubst (unProg program :: Dag.JetDag WhatIf () ())) :: TermWeight () ())
      let (encoded,witnessData)=Jets.putTermLengthCode (unProg program)
      mProgBits m @?= length encoded
      mWitBits m @?= length witnessData
  , testCase "measurement checkpoint round-trip and stale-input rejection" $ do
      let acquire = do
            tmp<-getTemporaryDirectory
            (dir,handle)<-openTempFile tmp "jet-discovery-checkpoint"
            hClose handle
            removeFile dir
            return dir
      bracket acquire removeDirectoryRecursive $ \dir -> do
        let program=Prog (((witness (w256FromBytes (BS.replicate 32 0))) &&& konst (w256FromBytes (BS.replicate 32 1))) >>> sha256Pair >>> unit)
            entry=Entry "checkpoint-unit" "checkpoint fixture" "library SHA256" BitcoinApp (Derived "local fixture") [] (const program) [Vector "honest" (const (Just env)) () Accept]
            result=runEntry entry
        saveResult dir "current-inputs" result
        loaded<-loadResult dir "current-inputs" entry
        case loaded of
          Nothing -> assertBool "missing round-trip" False
          Just r -> do
            mCmr (erMeasure r) @?= mCmr (erMeasure result)
            mCost (erMeasure r) @?= mCost (erMeasure result)
            mCandidateCosts (erMeasure r) @?= mCandidateCosts (erMeasure result)
            map niCmr (mProfile (erMeasure r)) @?= map niCmr (mProfile (erMeasure result))
        stale<-loadResult dir "changed-inputs" entry
        assertBool "stale inputs cannot reuse a measurement" (isNothing stale)
  , testCase "assumed witness budget uses CompactSize boundaries" $ do
      assumedWitnessStackBytes [] @?= 1
      map assumedWitnessStackBytes [[252],[253],[65535],[65536],[4294967296]] @?= [254,257,65539,65542,4294967306]
      assumedWitnessStackBytes (replicate 253 0) @?= 256
  , testCase "CMR mining combines type instantiations before computing share" $ do
      let p=Prog ((((witness (W.toWord W.word1024 0) &&& konst (W.toWord W.word1024 1)) >>> eq >>> verify) &&&
                   ((witness (W.toWord W.word1024 0,W.toWord W.word1024 0) &&& konst (W.toWord W.word1024 1,W.toWord W.word1024 1)) >>> eq >>> verify)) >>> unit)
          e=Entry "mining-types" "typed witness fixture" "local fixture" BitcoinApp (Derived "local fixture") [] (const p) [Vector "reject" (const (Just env)) () Reject]
          result=runEntry e
          [g]=filter ((=="witness").gKind) (mine False [result])
      gOccurrences g @?= 2
      length (gSig g) @?= 2
      gMaxShare g @?= fromInteger (gTotal g)/fromInteger (mCost (erMeasure result))
  , testCase "isolated candidate costs match independent substitution" $ do
      let rec=Prog (witness (W.toWord256 123,(W.toWord256 456,(W.toWord256 789,Left ()))) >>> Contract.ecRecover >>> unit)
          branch=Prog ((witness (Left () :: Either () ()) &&& unit) >>> cond
            (konst (W.toWord512 1) >>> sha256Pair >>> unit)
            (witness (W.toWord256 123,(W.toWord256 456,(W.toWord256 789,Left ()))) >>> Contract.ecRecover >>> unit))
          padded=Prog (witness (vec32 (map W.toWord64 [0..31])) >>> Hashes.keccakF >>> unit)
          check p name=do
            let Just (cost,count)=lookup name (mCandidateCosts (measure p))
            cost @?= directIsolatedCost name p
            assertBool "nonnegative static multiplicity" (count>=0)
      mapM_ (check rec) ["ecrecover","keccak_f1600","sha256_pair"]
      mapM_ (check branch) ["ecrecover","keccak_f1600","sha256_pair"]
      mapM_ (check padded) ["keccak_f1600","sha256_pair"]
      let Just (_,nested)=lookup "keccak_f1600" (mCandidateCosts (measure rec))
      nested @?= 1
  , testCase "restricted jet costs match independent substitution" $ do
      let sha=Prog (witness (W.toWord512 1) >>> sha256Pair >>> unit)
          curve=Prog (witness ((W.toWord256 1,W.toWord256 2),W.toWord256 1) >>> Secp.gej_double >>> unit)
          branch=Prog ((witness (Left () :: Either () ()) &&& unit) >>> cond
            (witness (W.toWord512 1) >>> sha256Pair >>> unit)
            (witness ((W.toWord256 1,W.toWord256 2),W.toWord256 1) >>> Secp.gej_double >>> unit))
          projection=Prog (((witness (W.toWord64 1) >>> Core.drop iden) &&& konst (W.toWord32 1)) >>> eq >>> verify)
          check p=do
            let dag=Dag.jetDag (unProg p :: Dag.JetDag Jets.JetType () ())
            primitiveCost dag @?= milliWeigh (Jets.unwrap (Dag.jetSubst (unProg p :: Dag.JetDag PrimOnly () ())) :: TermWeight () ())
            restrictedCost "no-secp-curve" dag @?= milliWeigh (Jets.unwrap (Dag.jetSubst (unProg p :: Dag.JetDag (Ablate NoSecpCurve) () ())) :: TermWeight () ())
            restrictedCost "no-secp" dag @?= milliWeigh (Jets.unwrap (Dag.jetSubst (unProg p :: Dag.JetDag (Ablate NoSecp) () ())) :: TermWeight () ())
            restrictedCost "no-sha256" dag @?= milliWeigh (Jets.unwrap (Dag.jetSubst (unProg p :: Dag.JetDag (Ablate NoSha256) () ())) :: TermWeight () ())
      mapM_ check [sha,curve,branch,projection]
  , testCase "standard SLH-DSA reference covers every supported NIST case" $ do
      contents<-readFile "vendor-specs/slhdsa/acvp-supported.tsv"
      let split s=case break (=='\t') s of (a,[])->[a];(a,_:rest)->a:split rest
          rows=map split (tail (lines contents))
      length rows @?= 28
      length (L.nub [(g,c)|[g,c,_,_,_,_]<-rows]) @?= 28
      mapM_ (\row->case row of
        [g,c,key,message,signature,expected]->do
          let pk=unhex key
              actual=case StandardSlh.parseSignature (unhex signature) of
                Nothing->False
                Just sig->StandardSlh.verifyInternal (BS.take 16 pk) (BS.drop 16 pk) (unhex message) sig
          BS.length pk @?= 32
          assertBool "invalid expected-result flag" (expected `elem` ["true","false"])
          assertBool ("NIST group/case "++g++"/"++c) (actual==(expected=="true"))
        _->assertBool "invalid standard ACVP TSV schema" False) rows
  , testCase "RFC8554 upstream LMS certificate" $ do
      Entry _ _ _ _ _ _ program vectors <- Lms.upstreamCertificate
      let cmr=progCmr (program (vecWitness (head vectors)))
      assertBool "upstream LMS certificate and corruption" (all vrOk (runVectors program cmr vectors))
  , testCase "Keccak-256 canonical digests" $ do
      Keccak.keccak256 BS.empty @?= unhex "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
      Keccak.keccak256 (BSC.pack "abc") @?= unhex "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"
  , testCase "BN254 candidate matches Integer reference" $ do
      let p=BN.pBN254
          xs=[(0,0),(1,p-1),(p-1,p-1),(2^253,2^253),(123456789,987654321)]
      mapM_ (\(a,b) -> fmap W.fromWord256 (run BN.fpMul (W.toWord256 a,W.toWord256 b)) @?= Just (a*b `mod`p)) xs
  , testCase "ECDSA and ecrecover candidates match Integer reference" $ do
      let sk=42; z=123456; k=17
          Just (qx,qy)=Bip340.pointMul Bip340.gPt sk
          Just (rx,ry)=Bip340.pointMul Bip340.gPt k
          r=rx `mod`Bip340.n
          pm _ 0=1
          pm b e | even e=let v=pm b (e `div`2) in v*v `mod`Bip340.n
                 | otherwise=b*pm b (e-1) `mod`Bip340.n
          sig=(z+r*sk)*pm k (Bip340.n-2) `mod`Bip340.n
          input=(((W.toWord256 qx,W.toWord256 qy),W.toWord256 z),(W.toWord256 r,W.toWord256 sig))
          rec zz=(W.toWord256 zz,(W.toWord256 r,(W.toWord256 sig,if odd ry then Right () else Left ())))
          address=Bip340.intFromBytes (Keccak.keccak256 (Bip340.bytesFromInt qx<>Bip340.bytesFromInt qy)) `mod`2^160
      run Contract.ecdsaVerify input @?= Just ()
      run Contract.ecdsaVerify (((W.toWord256 qx,W.toWord256 qy),W.toWord256 (z+1)),(W.toWord256 r,W.toWord256 sig)) @?= Nothing
      fmap W.fromWord256 (run Contract.ecRecover (rec z)) @?= Just address
      assertBool "changed recovery digest" (fmap W.fromWord256 (run Contract.ecRecover (rec (z+1))) /= Just address)
  , bip340Tests
  , p256Tests
  , testCase "RIPEMD-160 reference reproduces the published digests" $ do
      Ripemd.ripemd160Ref BS.empty @?= unhex "9c1185a5c5e9fc54612808977ee8f548b2258d31"
      Ripemd.ripemd160Ref (BSC8.pack "abc") @?= unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
      Ripemd.ripemd160Ref (BSC8.pack "message digest") @?= unhex "5d0689ef49d2fae572b881b123a85ffa21595f36"
  , testGroup "candidate specifications agree with Haskell references"
    [ testCase "m31_mul" $ do
        let xs = take 40 [ (a `mod` Stark.p31, b `mod` Stark.p31) | (a, b) <- pairs (rands 1) ]
        mapM_ (\(a, b) -> fmap W.fromWord32 (run Stark.m31Mul (W.toWord32 a, W.toWord32 b)) @?= Just (Stark.hMul a b)) xs
    , testCase "qm31_mul" $ do
        let qs = take 10 [ ((a, b), (c, d)) | [a, b, c, d] <- chunks 4 (map (`mod` Stark.p31) (rands 2)) ]
        mapM_ (\(x, y) -> run Stark.qm31Mul (Stark.toQ x, Stark.toQ y) @?= Just (Stark.toQ (Stark.hQMul x y))) (zip qs (reverse qs))
    , testCase "sha256_pair" $ do
        let bs = BS.pack (map fromIntegral (take 64 (rands 3)))
        fmap w256ToBytes (run sha256Pair (W.toWord512 (Bip340.intFromBytes bs))) @?= Just (hashToBytes (sha256 bs))
    , testCase "sha256_wots_chain_16" $ do
        let pkSeed = BS.replicate 16 0x5e
            (h, idx, chain) = (251, 5, 7)
            prefix = ctx8Init &&& konst (W.toWord512 (Bip340.intFromBytes (pkSeed <> BS.replicate 48 0))) >>> ctx8Add64
                 >>> (iden &&& konst (w8 h) >>> ctx8Add1) >>> (iden &&& konst (w64 idx) >>> ctx8Add8)
                 >>> (iden &&& konst (w8 16) >>> ctx8Add1) >>> (iden &&& konst (w32 0) >>> ctx8Add4)
                 >>> (iden &&& konst (w32 chain) >>> ctx8Add4)
            Just ctx = run prefix ()
            node = BS.pack [1 .. 16]
        mapM_ (\start -> fmap (\w -> BS.drop 16 (Bip340.bytesFromInt (W.fromWord128 w)))
                              (run wotsChain (ctx, (W.toWord4 (toInteger start), W.toWord128 (Bip340.intFromBytes node))))
                         @?= Just (Shrincs.wotsChainIter node start 15 pkSeed (fromInteger h) idx chain)) [0, 1, 7, 15]
    , testCase "sha256_wots_chain_16_fixed" $ do
        let bytes128 w=BS.drop 16 (Bip340.bytesFromInt (W.fromWord128 w))
            check state fields@(layer,tree,domain,keypair,chain) start node=do
              let Just prefix=ShrincsHashRef.encodePrefix fields
                  input=(w256FromBytes state,(((W.toWord8 layer,W.toWord64 tree),(W.toWord8 domain,(W.toWord32 keypair,W.toWord32 chain))),(W.toWord4 (toInteger start),W.toWord128 (Bip340.intFromBytes node))))
              fmap bytes128 (run ShrincsHash.chainRef input) @?= ShrincsHashRef.chainSpec state prefix start node
              fmap bytes128 (run ShrincsHash.chain input) @?= ShrincsHashRef.chainSpec state prefix start node
        mapM_ (\(seed,fields,start,node)->do
          let Just state=ShrincsHashRef.seedStateSpec seed
          fmap w256ToBytes (run ShrincsHash.seedState (W.toWord128 (Bip340.intFromBytes seed))) @?= Just state
          check state fields start node) ShrincsHashRef.seededCases
        mapM_ (\start->check (BS.pack [0..31]) (255,2^64-1,16,2^32-1,2^32-1) start (BS.pack [0..15])) [0,7,15]
        let program=Prog (witness (w256FromBytes (BS.pack [0..31]),(((W.toWord8 1,W.toWord64 2),(W.toWord8 0,(W.toWord32 3,W.toWord32 4))),(W.toWord4 7,W.toWord128 5))) >>> ShrincsHash.chain >>> unit)
        lookup "jet:cand:sha256_wots_chain_16_fixed" (mWhatIfJets (measure program)) @?= Just 1
    , testCase "keccak_f1600" $ do
        let st = take 25 (map fromInteger (rands 4)) :: [Word64]
            toV ls = vec32 (map (W.toWord64 . toInteger) (ls ++ replicate 7 0))
        fmap (map (fromInteger . W.fromWord64) . take 25 . unvec32) (run Hashes.keccakF (toV st)) @?= Just (keccakRef st)
    , testCase "blake2s_compress" $ do
        let hs = map fromInteger (take 8 (rands 5)) :: [Word32]
            ms = map fromInteger (take 16 (rands 6)) :: [Word32]
            v8 = vec8 . map (W.toWord32 . toInteger)
        fmap (map (fromInteger . W.fromWord32) . unvec8) (run (Hashes.blake2F Hashes.blake2s) ((v8 hs, (v8 (take 8 ms), v8 (drop 8 ms))), (W.toWord32 64, W.toWord32 0)))
          @?= Just (blake2sRef hs ms 64)
    , testCase "div_mod_256 and multiply_128" $ do
        let xs = take 20 (pairs (map (\x -> x * x * x * x) (rands 7)))
        mapM_ (\(a, b) -> do
                 let a' = a `mod` 2 ^ (256 :: Int); b' = 1 + b `mod` 2 ^ (200 :: Int)
                 fmap (\(q, r) -> (W.fromWord256 q, W.fromWord256 r)) (run (Arith.div_mod W.word256) (W.toWord256 a', W.toWord256 b')) @?= Just (a' `divMod` b')
                 let c = a `mod` 2 ^ (128 :: Int); d = b `mod` 2 ^ (128 :: Int)
                 fmap W.fromWord256 (run (Arith.multiply W.word128) (W.toWord128 c, W.toWord128 d)) @?= Just (c * d)) xs
    , testCase "multiply_256 and div_mod_512" $ do
        let xs = take 12 (pairs (map (\x -> x ^ (8 :: Int) + x) (rands 11)))
        mapM_ (\(a, b) -> do
                 let a' = a `mod` 2 ^ (256 :: Int); b' = b `mod` 2 ^ (256 :: Int)
                 fmap W.fromWord512 (run (Arith.multiply W.word256) (W.toWord256 a', W.toWord256 b')) @?= Just (a' * b')
                 let n = a' * b' + b'; d = 1 + b' `mod` 2 ^ (190 :: Int)
                 fmap (\(q, r) -> (W.fromWord512 q, W.fromWord512 r)) (run (Arith.div_mod W.word512) (W.toWord512 n, W.toWord512 d)) @?= Just (n `divMod` d)) xs
    , testCase "ripemd160_compress (one padded block of \"abc\")" $ do
        let le bs = sum [ toInteger b * 256 ^ i | (i, b) <- zip [0 :: Int ..] (BS.unpack bs) ]
            wordsLE bs = [ le (BS.take 4 (BS.drop (4 * i) bs)) | i <- [0 .. BS.length bs `div` 4 - 1] ]
            blk = wordsLE (BSC8.pack "abc\x80" <> BS.replicate 52 0) ++ [24, 0]
            v16 ws = (vec8 (map W.toWord32 (take 8 ws)), vec8 (map W.toWord32 (drop 8 ws)))
            out = run Rmd.ripemd160Compress (Rmd.toW5 Rmd.ripemdIV, v16 blk)
            flat (a, (b, (c, (d, e)))) = map W.fromWord32 [a, b, c, d, e]
        fmap flat out @?= Just (wordsLE (unhex "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"))
    , testCase "sha512_compress (one padded block of \"abc\", FIPS 180-4)" $ do
        let be bs = foldl (\acc b -> acc * 256 + toInteger b) 0 (BS.unpack bs)
            words64 bs = [ be (BS.take 8 (BS.drop (8 * i) bs)) | i <- [0 .. BS.length bs `div` 8 - 1] ]
            iv = [0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]
            blk = words64 (BSC8.pack "abc\x80" <> BS.replicate 116 0) ++ [24]
            v8' = vec8 . map W.toWord64
        fmap (map W.fromWord64 . unvec8) (run Ed.sha512Compress (v8' iv, (v8' (take 8 blk), v8' (drop 8 blk))))
          @?= Just (words64 (unhex "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"))
    , testCase "ed25519_fe_multiply" $ do
        let p = 2 ^ (255 :: Int) - 19
            xs = take 30 [ (a `mod` p, b `mod` p) | (a, b) <- pairs (map (\x -> x ^ (5 :: Int) + x) (rands 13)) ] ++ [(p - 1, p - 1), (0, p - 1), (1, 1)]
        mapM_ (\(a, b) -> fmap W.fromWord256 (run Ed.mulmod (W.toWord256 a, W.toWord256 b)) @?= Just (a * b `mod` p)) xs
    ]
  ]
 where
  pairs (a:b:r) = (a, b) : pairs r
  pairs _ = []
  chunks n xs = let (a, b) = splitAt n xs in a : chunks n b

-- Prepared execution must retain canonical source, environment and CMR
-- behavior even when witness types are partially erased or kernels change.
preparedTests :: TestTree
preparedTests = testGroup "prepared bound kernel"
  [ testCase "projection and branches agree with canonical full substitution" $ do
      let kernel :: Term.Simplicity term => term (W.Word8,W.Word1024) ()
          kernel=Core.oh >>> ((iden &&& konst (w8 0)) >>> eq >>> verify)
          prepared=boundProgram kernel
          raw value=Prog (witness value >>> kernel)
          values=[(w8 0,W.toWord W.word1024 1),(w8 1,W.toWord W.word1024 2)]
          vectors=zipWith (\value expected->Vector (show expected) (const (Just env)) value expected) values [Accept,Reject]
          cmr=progCmr (raw (head values))
      map (progCmr.prepared) values @?= map (progCmr.raw) values
      map vrOk (runVectors prepared cmr vectors) @?= [True,True]
      map vrOk (runVectors prepared cmr vectors) @?= map (vrOk.runVector prepared cmr) vectors
      let (p0,w0)=Jets.putTermLengthCode (unProg (raw (head values)))
          (p1,w1)=Jets.putTermLengthCode (unProg (prepared (head values)))
      (p1,w1) @?= (p0,w0)
      mCost (measure (prepared (head values))) @?= mCost (measure (raw (head values)))
      let branch :: Term.Simplicity term => term (Either W.Word8 W.Word8) ()
          branch=Core.copair ((iden &&& konst (w8 0)) >>> eq >>> verify) ((iden &&& konst (w8 1)) >>> eq >>> verify)
          bp=boundProgram branch
          vs=[Vector "left" (const (Just env)) (Left (w8 0)) Accept,Vector "right" (const (Just env)) (Right (w8 1)) Accept,Vector "wrong" (const (Just env)) (Right (w8 0)) Reject]
      map vrOk (runVectors bp (progCmr (bp (Left (w8 0)))) vs) @?= [True,True,True]
      assertBool "both branches really use prepared evaluation" (all (L.isSuffixOf "(prepared kernel)".vrNote) (runVectors bp (progCmr (bp (Left (w8 0)))) vs))
  , testCase "script CMR primitive receives the whole program environment" $ do
      let kernel :: (Term.Simplicity term,Term.Primitive term) => term W.Word256 ()
          kernel=(iden &&& (unit >>> Term.primitive Prim.ScriptCMR)) >>> eq >>> verify
          p=boundProgram kernel
          cmr=progCmr (p (W.toWord256 0))
          vector value expected=Vector "script root" (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap) value expected
          vs=[vector (W.toWord256 (hashToInteger cmr)) Accept,vector (W.toWord256 0) Reject]
      map vrOk (runVectors p cmr vs) @?= [True,True]
      map vrOk (runVectors p cmr vs) @?= map (vrOk.runVector p cmr) vs
      assertBool "environment case really uses prepared evaluation" (all (L.isSuffixOf "(prepared kernel)".vrNote) (runVectors p cmr vs))
  , testCase "source changes and unsafe extensions take canonical fallback" $ do
      let zero :: Term.Simplicity term => term W.Word8 ()
          zero=(iden &&& konst (w8 0)) >>> eq >>> verify
          one :: Term.Simplicity term => term W.Word8 ()
          one=(iden &&& konst (w8 1)) >>> eq >>> verify
          changed flag=(if flag then boundProgram one else boundProgram zero) (w8 0)
          vs=[Vector "original" (const (Just env)) False Accept,Vector "changed" (const (Just env)) True Reject]
          cmr=progCmr (changed False)
      map vrOk (runVectors changed cmr vs) @?= [True,False]
      map vrOk (runVectors changed cmr vs) @?= map (vrOk.runVector changed cmr) vs
      let changedType flag=if flag
            then boundProgram ((iden &&& konst (W.toWord16 0)) >>> eq >>> verify) (W.toWord16 0)
            else boundProgram zero (w8 0)
          tc=progCmr (changedType False)
          tvs=[Vector "byte" (const (Just env)) False Accept,Vector "word" (const (Just env)) True Accept]
      map vrOk (runVectors changedType tc tvs) @?= [True,False]
      map vrOk (runVectors changedType tc tvs) @?= map (vrOk.runVector changedType tc) tvs
      let internal :: Term.Simplicity term => term W.Word8 ()
          internal=witness (w8 0) >>> zero
          delegated :: Term.Simplicity term => term W.Word8 ()
          delegated=Core.disconnect (unit &&& unit) unit >>> unit
          eligible p=case boundView p of Just (BoundView k _)->boundEligible k; Nothing->True
      map eligible [boundProgram internal (w8 0),boundProgram delegated (w8 0)] @?= [False,False]
      mapM_ (\make->let c=progCmr (make (w8 0)); v=Vector "fallback" (const (Just env)) (w8 0) Accept in
        map vrOk (runVectors make c [v]) @?= [vrOk (runVector make c v)]) [boundProgram internal,boundProgram delegated]
  ]
-- BIP 340 vectors ----------------------------------------------------------------

bip340Tests :: TestTree
bip340Tests = testCase "Ref.Bip340 reproduces bip-0340_test-vectors.csv" $ do
  rows <- map (splitOn ',') . drop 1 . lines <$> readFile "vendor-specs/bips/bip-0340_test-vectors.csv"
  mapM_ check rows
 where
  check (i:sk:pk:aux:msg:sig:res:_) = do
    let ok = Bip340.verify (unhex pk) (unhex msg) (unhex sig)
    assertBool ("verify row " ++ i) (ok == (res == "TRUE"))
    if null sk then return () else do
      let s = Bip340.sign (Bip340.intFromBytes (unhex sk)) (unhex msg) (unhex aux)
      assertBool ("sign row " ++ i) (s == unhex sig)
  check r = assertBool ("bad row " ++ show r) False
  splitOn c s = case break (== c) s of
    (a, []) -> [a]
    (a, _:r) -> a : splitOn c r

-- Haskell references ---------------------------------------------------------------

keccakRef :: [Word64] -> [Word64]
keccakRef st0 = foldl roundF st0 [0 .. 23]
 where
  rc = [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
       , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
       , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
       , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]
  rot x y = [[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]] !! x !! y
  at a x y = a !! (x + 5 * y)
  roundF a r = iota
   where
    c x = foldr1 xor [ at a x y | y <- [0 .. 4] ]
    d x = c ((x + 4) `mod` 5) `xor` (c ((x + 1) `mod` 5) `rotateL` 1)
    th = [ at a x y `xor` d x | y <- [0 .. 4], x <- [0 .. 4] ]
    b = [ head [ (at th x y) `rotateL` rot x y | x <- [0 .. 4], y <- [0 .. 4], y' == y && x' == (2 * x + 3 * y) `mod` 5 ]
        | y' <- [0 .. 4], x' <- [0 .. 4] ]
    -- b is indexed [x' + 5 y'] with B[y, 2x+3y] = rot(A[x,y]): position (x'=y? ) handled below
    bArr = [ head [ (at th x y) `rotateL` rot x y | x <- [0 .. 4], y <- [0 .. 4], y + 5 * ((2 * x + 3 * y) `mod` 5) == j ] | j <- [0 .. 24] ]
    chi = [ (bArr !! (x + 5 * y)) `xor` (complement (bArr !! (((x + 1) `mod` 5) + 5 * y)) .&. (bArr !! (((x + 2) `mod` 5) + 5 * y))) | y <- [0 .. 4], x <- [0 .. 4] ]
    iota = (head chi `xor` (rc !! r)) : tail chi

blake2sRef :: [Word32] -> [Word32] -> Word32 -> [Word32]
blake2sRef h m t = [ (h !! i) `xor` (v !! i) `xor` (v !! (i + 8)) | i <- [0 .. 7] ]
 where
  iv = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
  sigma = [ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15], [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3]
          , [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4], [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8]
          , [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13], [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9]
          , [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11], [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10]
          , [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5], [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0] ]
  v0 = h ++ take 4 iv ++ [iv !! 4 `xor` t, iv !! 5, complement (iv !! 6), iv !! 7]
  v = foldl rnd v0 [0 .. 9]
  set vs i x = take i vs ++ [x] ++ drop (i + 1) vs
  g vs (a, b, c, d) x y =
    let va1 = vs !! a + vs !! b + x; vd1 = (vs !! d `xor` va1) `rotateR` 16; vc1 = vs !! c + vd1; vb1 = (vs !! b `xor` vc1) `rotateR` 12
        va2 = va1 + vb1 + y; vd2 = (vd1 `xor` va2) `rotateR` 8; vc2 = vc1 + vd2; vb2 = (vb1 `xor` vc2) `rotateR` 7
    in set (set (set (set vs a va2) b vb2) c vc2) d vd2
  rnd vs r = let s = sigma !! r
                 ls = [(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),(0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]
             in foldl (\acc (i, l) -> g acc l (m !! (s !! (2 * i))) (m !! (s !! (2 * i + 1)))) vs (zip [0 ..] ls)

-- nested-pair vectors
vec8 :: [a] -> ((((a, a), (a, a)), ((a, a), (a, a))))
vec8 [a, b, c, d, e, f, g, h] = (((a, b), (c, d)), ((e, f), (g, h)))
vec8 _ = error "vec8"
unvec8 :: ((((a, a), (a, a)), ((a, a), (a, a)))) -> [a]
unvec8 (((a, b), (c, d)), ((e, f), (g, h))) = [a, b, c, d, e, f, g, h]
vec32 :: [a] -> (((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))), ((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))))
vec32 xs = ((vec8 (s 0), vec8 (s 1)), (vec8 (s 2), vec8 (s 3))) where s i = take 8 (drop (8 * i) xs)
unvec32 :: (((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a)))), ((((a, a), (a, a)), ((a, a), (a, a))), (((a, a), (a, a)), ((a, a), (a, a))))) -> [a]
unvec32 ((a, b), (c, d)) = concatMap unvec8 [a, b, c, d]

-- P-256 field and group operations ------------------------------------------------------------

p256Tests :: TestTree
p256Tests = testGroup "P-256 Simplicity arithmetic agrees with Integer arithmetic"
  [ testCase "mulmod" $ mapM_ (\(a, b) -> fmap W.fromWord256 (run P256.mulmod (W.toWord256 a, W.toWord256 b)) @?= Just (a * b `mod` p)) xs
  , testCase "addmod and submod" $ mapM_ (\(a, b) -> do
        fmap W.fromWord256 (run P256.addmod (W.toWord256 a, W.toWord256 b)) @?= Just ((a + b) `mod` p)
        fmap W.fromWord256 (run P256.submod (W.toWord256 a, W.toWord256 b)) @?= Just ((a - b) `mod` p)) xs
  , testCase "ECDSA x-coordinate never wraps r+n" $ do
        let n=P256.nP256
            cases=[(1,1,1,True),(1,n+1,1,True),(2^256-n+1,1,1,False),(1,2,1,False),(7,63,3,True)]
        mapM_ (\(r,x,z,ok) -> run P256.ecdsaXCoordinate (W.toWord256 r,(W.toWord256 x,W.toWord256 z)) @?= Just (if ok then Right () else Left ())) cases
  , testCase "complete P-256 additions handle equality, opposites and infinity" $ do
        let q=(W.toWord256 gx,W.toWord256 gy)
            minusQ=(W.toWord256 gx,W.toWord256 (p-gy))
            j=toJ ((gx,gy),1)
        fmap (\(flag,v)->(flag,affine (fromJ v))) (run P256.addAffine (q,(Left (),j))) @?= Just (Left (),affine (dblRef (gx,gy)))
        fmap fst (run P256.addAffine (minusQ,(Left (),j))) @?= Just (Right ())
        fmap (\(flag,v)->(flag,affine (fromJ v))) (run P256.addAffine (q,(Right (),toJ ((0,0),0)))) @?= Just (Left (), (gx,gy))
  , testCase "dblJ and maddJ" $ do
        let j = ((gx, gy), 1)
            Just d = run P256.dblJ (toJ j)
            Just a = run P256.maddJ (d, (W.toWord256 gx, W.toWord256 gy))
        affine (fromJ d) @?= affine (dblRef (gx, gy))
        affine (fromJ a) @?= affine (addRef (dblRef (gx, gy)) (gx, gy))
  ]
 where
  p = P256.pP256
  gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
  gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
  xs = take 30 [ (a `mod` p, b `mod` p) | (a, b) <- pairs (map (\x -> x * x * x * x + x) (rands 9)) ] ++ [(p - 1, p - 1), (0, p - 1), (1, 1)]
  pairs (a:b:r) = (a, b) : pairs r
  pairs _ = []
  inv x = powM x (p - 2)
  powM _ 0 = 1
  powM b e | even e = let h = powM b (e `div` 2) in h * h `mod` p
           | otherwise = b * powM b (e - 1) `mod` p
  toJ ((x, y), z) = ((W.toWord256 x, W.toWord256 y), W.toWord256 z)
  fromJ ((x, y), z) = ((W.fromWord256 x, W.fromWord256 y), W.fromWord256 z)
  affine ((x, y), z) = (x * inv (z * z) `mod` p, y * inv (z * z * z) `mod` p)
  dblRef (x, y) = let l = (3 * x * x - 3) * inv (2 * y) `mod` p; x3 = (l * l - 2 * x) `mod` p in ((x3, (l * (x - x3) - y) `mod` p), 1)
  addRef ((x1, y1), _) (x2, y2) = let l = (y2 - y1) * inv (x2 - x1) `mod` p; x3 = (l * l - x1 - x2) `mod` p in ((x3, (l * (x1 - x3) - y1) `mod` p), 1)
