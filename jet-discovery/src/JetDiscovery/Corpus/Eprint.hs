{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Constructions from the cryptography literature with a Bitcoin deployment
-- path, built from the existing secp256k1 jets:
--
-- * BIP 340 adaptor-signature (pre-signature) verification (PTLCs, DLCs, swaps);
-- * BIP 327 MuSig2 KeyAgg of three keys, checked against BIP 327's vectors;
-- * a 4-key Schnorr ring signature (AOS; proof of reserves without revealing which key);
-- * a Chaum-Pedersen DLEQ proof, as used by Cashu ecash (NUT-12).
module JetDiscovery.Corpus.Eprint
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

type GE = (Word256, Word256)

kw :: (Core term, TyC s) => Integer -> term s Word256
kw = konst . toWord256

toGEJ :: (Core term, TyC s) => term s GE -> term s (GE, Word256)
toGEJ t = t &&& kw 1

normalize :: Assert term => term (GE, Word256) GE
normalize = Secp.gej_normalize >>> verify

liftX :: Assert term => term Word256 GE
liftX = (false &&& iden) >>> Secp.decompress >>> verify

onCurve :: Assert term => term GE ()
onCurve = Secp.ge_is_on_curve >>> verify

-- Adaptor signatures --------------------------------------------------------------------

-- | Pre-signature (R', s') for adaptor point T under key P on message m:
-- R = R' + T has even y, e = hash_BIP0340/challenge(x(R) || P || m), and s' G = R' + e P.
adaptorVerify :: forall term. (Assert term, Witness term) => ((Word256, Word256), ((GE, GE), Word256)) -> term () ()
adaptorVerify ((pv, mv), ((r'v, tv), s'v)) = ((r' >>> onCurve) &&& (t >>> onCurve)) &&& (evenR &&& lin) >>> unit
 where
  r', t :: forall a. TyC a => term a GE
  r' = witness r'v
  t = witness tv
  rPt :: term () GE
  rPt = (toGEJ r' &&& t) >>> Secp.gej_ge_add >>> normalize
  evenR = rPt >>> ih >>> Secp.fe_is_odd >>> not iden >>> verify
  e = ((((unit >>> ctx8InitTag "BIP0340/challenge") &&& (rPt >>> oh) >>> ctx8Add32) &&& witness pv >>> ctx8Add32) &&& witness mv >>> ctx8Add32) >>> ctx8Finalize >>> Secp.scalar_normalize
  lin = ((((e >>> Secp.scalar_negate) &&& (witness pv >>> liftX)) &&& witness s'v) &&& r') >>> Secp.linear_verify_1

-- MuSig2 KeyAgg --------------------------------------------------------------------------

type CKey = (Word8, Word256)   -- compressed key: (prefix, x)

-- | x(Q) for Q = sum a_i P_i (BIP 327 KeyAgg, three keys).
keyAgg3 :: forall term. (Assert term, Witness term) => ([CKey], Word256) -> term () ()
keyAgg3 (ks, expected) = (valid &&& ((qx &&& witness expected) >>> eq >>> verify)) >>> unit
 where
  k :: Int -> (forall a. TyC a => term a CKey)
  k i = witness (ks !! i)
  keyAdd :: Int -> term Ctx8 Ctx8
  keyAdd i = ctxWith (k i >>> oh) ctx8Add1 >>> ctxWith (k i >>> ih) ctx8Add32
  -- L = hash_KeyAgg list(pk1 || pk2 || pk3)
  lHash :: term () Word256
  lHash = (unit >>> ctx8InitTag "KeyAgg list") >>> keyAdd 0 >>> keyAdd 1 >>> keyAdd 2 >>> ctx8Finalize
  same :: Int -> Int -> term () Bit
  same i j = and (((k i >>> oh) &&& (k j >>> oh)) >>> eq) (((k i >>> ih) &&& (k j >>> ih)) >>> eq)
  -- GetSecondKey: pk_i gets coefficient 1 iff it equals the first key differing from pk1
  isSecond :: Int -> term () Bit
  isSecond 0 = false
  isSecond 1 = not (same 1 0)
  isSecond _ = (same 1 0 &&& unit) >>> cond (not (same 2 0)) (same 2 1)
  coeff :: Int -> term () Word256
  coeff i = (isSecond i &&& unit) >>> cond (kw 1)
              (((unit >>> ctx8InitTag "KeyAgg coefficient") >>> ctxWith lHash ctx8Add32 >>> keyAdd i >>> ctx8Finalize) >>> Secp.scalar_normalize)
  point :: Int -> term () GE
  point i = (((k i >>> oh) &&& konst (w8 3) >>> eq) &&& (k i >>> ih)) >>> Secp.decompress >>> verify
  scaled :: Int -> term () (GE, Word256)
  scaled i = (coeff i &&& toGEJ (point i)) >>> Secp.scale
  qx = ((scaled 0 &&& scaled 1) >>> Secp.gej_add) &&& scaled 2 >>> Secp.gej_add >>> normalize >>> oh
  -- prefix 2 or 3, and x below the field size
  validKey :: Int -> term () ()
  validKey i = (or (((k i >>> oh) &&& konst (w8 2)) >>> eq) (((k i >>> oh) &&& konst (w8 3)) >>> eq) >>> verify)
               &&& (((k i >>> ih) &&& kw Ref.p >>> Arith.subtract word256) >>> oh >>> verify) >>> unit
  valid = (validKey 0 &&& (validKey 1 &&& validKey 2)) >>> unit

-- Ring signature ----------------------------------------------------------------------------

-- | AOS ring signature over keys P_0..P_3 on m: R_i = s_i G - e_i P_i, e_{i+1} = H(m || R_i), e_4 = e_0.
ringVerify :: forall term. (Assert term, Witness term) => (([Word256], Word256), (Word256, [Word256])) -> term () ()
ringVerify ((pks, mv), (e0v, ss)) = (L.foldl' (\acc i -> acc >>> link i) (witness e0v) [0 .. 3] &&& witness e0v) >>> eq >>> verify
 where
  link i = (((Secp.scalar_negate &&& (unit >>> witness (pks !! i) >>> liftX >>> toGEJ iden)) &&& (unit >>> witness (ss !! i))) >>> Secp.linear_combination_1 >>> normalize)
           >>> ((((unit >>> ctx8Init) &&& (unit >>> witness mv) >>> ctx8Add32) &&& iden >>> ctx8Add64) >>> ctx8Finalize >>> Secp.scalar_normalize)

-- DLEQ ------------------------------------------------------------------------------------

-- | Chaum-Pedersen proof (e, s) that log_G(A) = log_B(C): R1 = s G - e A, R2 = s B - e C, e = H(R1 || R2 || A || C).
dleqVerify :: forall term. (Assert term, Witness term) => ((GE, (GE, GE)), (Word256, Word256)) -> term () ()
dleqVerify ((av, (bv, cv)), (ev, sv)) = ((onCurve' a &&& (onCurve' b &&& onCurve' c)) &&& ((eT &&& witness ev) >>> eq >>> verify)) >>> unit
 where
  a, b, c :: forall x. TyC x => term x GE
  a = witness av
  b = witness bv
  c = witness cv
  onCurve' t = t >>> onCurve
  negE = witness ev >>> Secp.scalar_negate
  r1 = ((negE &&& toGEJ a) &&& witness sv) >>> Secp.linear_combination_1 >>> normalize
  r2 = ((witness sv &&& toGEJ b) >>> Secp.scale) &&& ((negE &&& toGEJ c) >>> Secp.scale) >>> Secp.gej_add >>> normalize
  eT = (ctx8Init >>> ctxWith r1 ctx8Add64 >>> ctxWith r2 ctx8Add64 >>> ctxWith a ctx8Add64 >>> ctxWith c ctx8Add64) >>> ctx8Finalize >>> Secp.scalar_normalize

-- Vectors ---------------------------------------------------------------------------------

n :: Integer
n = Ref.n

ptW :: Ref.Pt -> GE
ptW (Just (x, y)) = (toWord256 x, toWord256 y)
ptW Nothing = error "infinity"

be32 :: Integer -> BS.ByteString
be32 = Ref.bytesFromInt

tagged :: String -> BS.ByteString -> Integer
tagged t m = Ref.intFromBytes (Ref.taggedHash t m)

entries :: IO [Entry]
entries = do
  kaRaw <- readFile "vendor-specs/bips/bip-0327_vectors_key_agg_vectors.json"
  let pubkeys = quoted (between "\"pubkeys\"" "]" kaRaw)
      cases = [ (map read (words (map (\ch -> if ch == ',' then ' ' else ch) idx)), ex) | (idx, ex) <- keyCases (between "\"valid_test_cases\"" "\"error_test_cases\"" kaRaw) ] :: [([Int], String)]
      ck h = let bs = unhex h in (w8 (toInteger (BS.head bs)), w256FromBytes (BS.drop 1 bs))
      kaVecs | length cases /= 4 || length pubkeys /= 7 = error "BIP 327 key_agg vectors: unexpected file layout"
             | otherwise = [ Vector ("BIP 327 key_agg valid case " ++ show is) env (map (ck . (pubkeys !!)) is, w256FromBytes (unhex ex)) Accept
               | (is, ex) <- cases, length is == 3 ]
               ++ [ Vector "BIP 327 key index 3 (x not on the curve)" env (map (ck . (pubkeys !!)) [0, 3, 1], toWord256 0) Reject
                  , Vector "BIP 327 key index 4 (x exceeds the field size)" env (map (ck . (pubkeys !!)) [0, 1, 4], toWord256 0) Reject
                  , Vector "BIP 327 key index 5 (invalid prefix 0x04)" env (map (ck . (pubkeys !!)) [5, 0, 1], toWord256 0) Reject
                  , Vector "valid keys [0,1,2] with the [2,1,0] aggregate (order matters)" env (map (ck . (pubkeys !!)) [0, 1, 2], w256FromBytes (unhex (snd (cases !! 1)))) Reject ]
  return
    [ Entry
      { entryId = "eprint-adaptor-sig"
      , entryTitle = "BIP 340 adaptor (pre-)signature verification"
      , entrySpec = "Schnorr adaptor signatures as used for PTLCs/DLCs (e.g. secp256k1-zkp's schnorr adaptor module)"
      , entryCategory = Eprint
      , entryVectorSource = Derived "pre-signatures from Ref.Bip340 point arithmetic; the adapted signature also passes Ref.Bip340.verify"
      , entryAssumptions = ["key, message, R', T and s' are witness operands"]
      , entryProgram = \w -> Prog (adaptorVerify w)
      , entryVectors =
          [ Vector ("valid pre-signature" ++ adaptorNote) env adaptorW Accept
          , Vector "pre-signature for another message" env (let ((p, _), r) = adaptorW in ((p, toWord256 5), r)) Reject
          , Vector "wrong adaptor point" env (let (pm, ((r', _), s')) = adaptorW in (pm, ((r', ptW (Ref.pointMul Ref.gPt 78)), s'))) Reject ]
      }
    , Entry
      { entryId = "eprint-musig2-keyagg"
      , entryTitle = "MuSig2 KeyAgg of three keys in-script (BIP 327)"
      , entrySpec = "BIP 327 KeyAgg (vendor-specs/bips/bip-0327.mediawiki)"
      , entryCategory = Eprint
      , entryVectorSource = Upstream "vendor-specs/bips/bip-0327_vectors_key_agg_vectors.json (3-key valid cases and invalid-key cases)"
      , entryAssumptions = ["exactly three compressed keys; keys and the expected x-only aggregate are witness operands"]
      , entryProgram = \w -> Prog (keyAgg3 w)
      , entryVectors = kaVecs
      }
    , Entry
      { entryId = "eprint-ring-sig"
      , entryTitle = "4-key Schnorr ring signature (AOS)"
      , entrySpec = "Abe-Ohkubo-Suzuki ring signatures over secp256k1 (e.g. proof of reserves without revealing the key)"
      , entryCategory = Eprint
      , entryVectorSource = Derived "ring signatures from a Haskell AOS signer over Ref.Bip340 point arithmetic"
      , entryAssumptions = ["ring of 4 x-only keys (even y); e_{i+1} = sha256(m || x(R_i) || y(R_i)) mod n"]
      , entryProgram = \w -> Prog (ringVerify w)
      , entryVectors =
          [ Vector "valid ring signature (signer index 2)" env ringW Accept
          , Vector "ring signature on another message" env (let ((ps, _), sg) = ringW in ((ps, toWord256 9), sg)) Reject ]
      }
    , Entry
      { entryId = "eprint-dleq-cashu"
      , entryTitle = "Chaum-Pedersen DLEQ proof (Cashu NUT-12 style)"
      , entrySpec = "Chaum-Pedersen discrete-log equality; Cashu NUT-12 blind-signature DLEQ"
      , entryCategory = Eprint
      , entryVectorSource = Derived "proofs from Ref.Bip340 point arithmetic"
      , entryAssumptions = ["transcript: sha256(R1 || R2 || A || C) over 64-byte affine points (NUT-12 hashes hex encodings)"]
      , entryProgram = \w -> Prog (dleqVerify w)
      , entryVectors =
          [ Vector "valid DLEQ proof" env dleqW Accept
          , Vector "C from a different secret" env (let ((a, (b, _)), es) = dleqW in ((a, (b, ptW (Ref.pointMul (Just bPt) 12345))), es)) Reject ]
      }
    ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  -- adaptor: choose k, t so that R = (k + t) G has even y
  x0 = 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef
  Just pP = Ref.pointMul Ref.gPt x0
  xs = if Ref.hasEvenY pP then x0 else n - x0
  pk = fst pP
  msgA = 0x4242
  (kA, tA) = head [ (k', t') | i <- [1 ..], let k' = 1000 + i, let t' = 77, Just rr <- [Ref.pointMul Ref.gPt (k' + t')], Ref.hasEvenY rr ]
  rPre = Ref.pointMul Ref.gPt kA
  tPt = Ref.pointMul Ref.gPt tA
  Just rFull = Ref.pointAdd rPre tPt
  eA = tagged "BIP0340/challenge" (be32 (fst rFull) <> be32 pk <> be32 msgA) `mod` n
  s'A = (kA + eA * xs) `mod` n
  adaptorW = ((toWord256 pk, toWord256 msgA), ((ptW rPre, ptW tPt), toWord256 s'A))
  adaptorNote = if Ref.verify (be32 pk) (be32 msgA) (be32 (fst rFull) <> be32 ((s'A + tA) `mod` n)) then "" else " (ADAPTED SIGNATURE INVALID)"
  -- ring: keys with even y; signer index 2
  ringSks = [ let Just q = Ref.pointMul Ref.gPt s in if Ref.hasEvenY q then s else n - s | s <- [111, 222, 333, 444] ]
  ringPks = [ fst q | s <- ringSks, let Just q = Ref.pointMul Ref.gPt s ]
  msgR = 0x99
  hR (Just (x, y)) = Ref.intFromBytes (hashToBytes (sha256 (be32 msgR <> be32 x <> be32 y))) `mod` n
  hR Nothing = error "ring: infinity"
  rI s e i = Ref.pointAdd (Ref.pointMul Ref.gPt s) (Ref.pointMul (Ref.liftX (ringPks !! i)) (n - e))
  kR = 5555
  -- e_3 from R_2 = k G, then forward through 3, 0, 1, close at 2
  e3 = hR (Ref.pointMul Ref.gPt kR)
  sFake = [9001, 9002, 9003, 9004]
  e0 = hR (rI (sFake !! 3) e3 3)
  e1 = hR (rI (sFake !! 0) e0 0)
  e2 = hR (rI (sFake !! 1) e1 1)
  s2 = (kR + e2 * (ringSks !! 2)) `mod` n
  ringW = ((map toWord256 ringPks, toWord256 msgR), (toWord256 e0, map toWord256 [sFake !! 0, sFake !! 1, s2, sFake !! 3]))
  -- DLEQ: A = a G, C = a B
  aSec = 0xabcdef
  Just aPt = Ref.pointMul Ref.gPt aSec
  Just bPt = Ref.pointMul Ref.gPt 0x777777
  Just cPt = Ref.pointMul (Just bPt) aSec
  rr = 0x31337
  Just r1 = Ref.pointMul Ref.gPt rr
  Just r2 = Ref.pointMul (Just bPt) rr
  ser (x, y) = be32 x <> be32 y
  eD = Ref.intFromBytes (hashToBytes (sha256 (ser r1 <> ser r2 <> ser aPt <> ser cPt))) `mod` n
  sD = (rr + eD * aSec) `mod` n
  dleqW = ((ptW (Just aPt), (ptW (Just bPt), ptW (Just cPt))), (toWord256 eD, toWord256 sD))
  -- minimal readers for key_agg_vectors.json
  between a b str = let r = snd (breakOn a str) in fst (breakOn b r)
  quoted str = case dropWhile (/= '"') str of
    [] -> []
    (_:r) -> let (x, r') = break (== '"') r in x : quoted (L.drop 1 r')
  keyCases str = [ (idx, ex) | blk <- L.drop 1 (splitOn "key_indices" str)
                             , let idx = L.takeWhile (/= ']') (L.drop 1 (dropWhile (/= '[') blk))
                             , let ex = head (quoted (snd (breakOn "expected" blk) `dropPast` ':')) ]
  dropPast str c = L.drop 1 (dropWhile (/= c) str)
  breakOn pat str = case L.findIndex (L.isPrefixOf pat) (L.tails str) of
    Just i -> (L.take i str, L.drop (i + length pat) str)
    Nothing -> (str, [])
  splitOn pat str = case breakOn pat str of
    (a, []) | not' (pat `L.isInfixOf` str) -> [a]
    (a, r) -> a : splitOn pat r
  not' b = if b then False else True
