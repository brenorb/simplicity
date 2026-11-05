{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Constructions from the cryptography literature with a Bitcoin deployment
-- path, built from the existing secp256k1 jets:
--
-- * BIP 340 adaptor-signature (pre-signature) verification (PTLCs, DLCs, swaps);
-- * BIP 327 MuSig2 KeyAgg of three keys, checked against BIP 327's vectors;
-- * a 4-key Schnorr ring signature (AOS; proof of reserves without revealing which key);
-- * a Chaum-Pedersen DLEQ proof, as used by Cashu ecash (NUT-12).
module JetDiscovery.Corpus.Eprint
  ( entries, adaptorT, ringT, dleqT, encodingProbes
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
liftX = (canonicalField &&& iden) >>> ih >>> (false &&& iden) >>> Secp.decompress >>> verify

onCurve :: Assert term => term GE ()
onCurve = ((oh >>> canonicalField) &&& ((ih >>> canonicalField) &&& (Secp.ge_is_on_curve >>> verify))) >>> unit

canonicalField :: Assert term => term Word256 ()
canonicalField=(iden &&& kw Ref.p) >>> Arith.lt word256 >>> verify
canonicalScalar :: Assert term => term Word256 ()
canonicalScalar=(iden &&& kw Ref.n) >>> Arith.lt word256 >>> verify

-- All multiply-used proof/key fields enter through one structured witness.
-- Context helpers preserve the bound input value, never re-witness fields.
appendT :: (Assert term,TyC a,TyC b) => term a b -> term (Ctx8,b) Ctx8 -> term (a,Ctx8) (a,Ctx8)
appendT f jet=oh &&& ((ih &&& (oh >>> f)) >>> jet)
startHash :: (Assert term,TyC a) => String -> term a (a,Ctx8)
startHash tag=iden &&& (unit >>> if null tag then ctx8Init else ctx8InitTag tag)
endHash :: (Assert term,TyC a) => term (a,Ctx8) Word256
endHash=drop ctx8Finalize

-- Adaptor signatures ---------------------------------------------------------
type AdaptorInput=((Word256,Word256),((GE,GE),Word256))
adaptorVerify :: (Assert term,Witness term) => AdaptorInput -> term () ()
adaptorVerify w=witness w >>> adaptorT
adaptorT :: forall term. Assert term => term AdaptorInput ()
adaptorT=((pk >>> canonicalField) &&& ((response >>> canonicalScalar) &&& (((r' >>> onCurve) &&& (t >>> onCurve)) &&& (evenR &&& lin)))) >>> unit
 where
  pk=ooh;message=oih
  r'=ih >>> oh >>> oh
  t=ih >>> oh >>> ih
  response=ih >>> ih
  rPt=(toGEJ r' &&& t) >>> Secp.gej_ge_add >>> normalize
  evenR=rPt >>> ih >>> Secp.fe_is_odd >>> not iden >>> verify
  e=startHash "BIP0340/challenge" >>> appendT (rPt >>> oh) ctx8Add32 >>> appendT pk ctx8Add32 >>> appendT message ctx8Add32 >>> endHash >>> Secp.scalar_normalize
  lin=((((e >>> Secp.scalar_negate) &&& (pk >>> liftX)) &&& response) &&& r') >>> Secp.linear_verify_1

-- MuSig2 KeyAgg --------------------------------------------------------------
type CKey=(Word8,Word256)
type KeyAggInput=((CKey,(CKey,CKey)),Word256)
keyAgg3 :: (Assert term,Witness term) => ([CKey],Word256) -> term () ()
keyAgg3 ([a,b,c],expected)=witness ((a,(b,c)),expected) >>> keyAggT
keyAgg3 _=error "KeyAgg3: expected3keys"
keyAggT :: forall term. Assert term => term KeyAggInput ()
keyAggT=(valid &&& ((qx &&& ih) >>> eq >>> verify)) >>> unit
 where
  k :: Int -> term KeyAggInput CKey
  k 0=oh >>> oh
  k 1=oh >>> ih >>> oh
  k 2=oh >>> ih >>> ih
  k _=error "KeyAgg index"
  keyAdd i=appendT (k i >>> oh) ctx8Add1 >>> appendT (k i >>> ih) ctx8Add32
  lHash=startHash "KeyAgg list" >>> keyAdd 0 >>> keyAdd 1 >>> keyAdd 2 >>> endHash
  same i j=and (((k i >>> oh) &&& (k j >>> oh)) >>> eq) (((k i >>> ih) &&& (k j >>> ih)) >>> eq)
  isSecond 0=false
  isSecond 1=not (same 1 0)
  isSecond _=(same 1 0 &&& iden) >>> cond (not (same 2 0)) (same 2 1)
  coeff i=(isSecond i &&& iden) >>> cond (kw 1)
          ((startHash "KeyAgg coefficient" >>> appendT lHash ctx8Add32 >>> keyAdd i >>> endHash) >>> Secp.scalar_normalize)
  point i=(((k i >>> oh) &&& konst (w8 3) >>> eq) &&& (k i >>> ih)) >>> Secp.decompress >>> verify
  scaled i=(coeff i &&& toGEJ (point i)) >>> Secp.scale
  qx=((scaled 0 &&& scaled 1) >>> Secp.gej_add) &&& scaled 2 >>> Secp.gej_add >>> normalize >>> oh
  validKey i=(or (((k i >>> oh) &&& konst (w8 2)) >>> eq) (((k i >>> oh) &&& konst (w8 3)) >>> eq) >>> verify)
             &&& (((k i >>> ih) &&& kw Ref.p >>> Arith.subtract word256) >>> oh >>> verify) >>> unit
  valid=(validKey 0 &&& (validKey 1 &&& validKey 2)) >>> unit

-- AOS ring signature ---------------------------------------------------------
type RingInput=((Vector4 Word256,Word256),(Word256,Vector4 Word256))
ringVerify :: (Assert term,Witness term) => (([Word256],Word256),(Word256,[Word256])) -> term () ()
ringVerify (([p0,p1,p2,p3],m),(e,[s0,s1,s2,s3]))=witness ((((p0,p1),(p2,p3)),m),(e,((s0,s1),(s2,s3)))) >>> ringT
ringVerify _=error "Ring: expected4keys/responses"
ringT :: forall term. Assert term => term RingInput ()
ringT=(canonical &&& cycleCheck) >>> unit
 where
  canonical=((ih >>> oh >>> canonicalScalar) &&& L.foldl' (\acc i -> (acc &&& ((oh >>> oh >>> item i >>> canonicalField) &&& (ih >>> ih >>> item i >>> canonicalScalar))) >>> unit) unit [0..3]) >>> unit
  cycleCheck=(iden &&& (ih >>> oh)) >>> L.foldl' (>>>) iden [link i | i<-[0..3]] >>> ((ih &&& (oh >>> ih >>> oh)) >>> eq >>> verify)
  -- State(bound entire input,current challenge).
  key i=oh >>> oh >>> oh >>> item i
  response i=oh >>> ih >>> ih >>> item i
  message=oh >>> oh >>> ih
  item 0=ooh;item 1=oih;item 2=ioh;item _=iih
  link i=oh &&& next
   where
    nonce=(((ih >>> Secp.scalar_negate) &&& (key i >>> liftX >>> toGEJ iden)) &&& response i) >>> Secp.linear_combination_1 >>> normalize
    next=startHash "" >>> appendT message ctx8Add32 >>> appendT nonce ctx8Add64 >>> endHash >>> Secp.scalar_normalize

-- Chaum-Pedersen DLEQ --------------------------------------------------------
type DleqInput=((GE,(GE,GE)),(Word256,Word256))
dleqVerify :: (Assert term,Witness term) => DleqInput -> term () ()
dleqVerify w=witness w >>> dleqT
dleqT :: forall term. Assert term => term DleqInput ()
dleqT=(((ih >>> oh >>> canonicalScalar) &&& (response >>> canonicalScalar)) &&& (((a >>> onCurve) &&& ((b >>> onCurve) &&& (c >>> onCurve))) &&& ((eT &&& (ih >>> oh)) >>> eq >>> verify))) >>> unit
 where
  a=oh >>> oh
  b=oh >>> ih >>> oh
  c=oh >>> ih >>> ih
  response=ih >>> ih
  negE=ih >>> oh >>> Secp.scalar_negate
  r1=((negE &&& toGEJ a) &&& response) >>> Secp.linear_combination_1 >>> normalize
  r2=((response &&& toGEJ b) >>> Secp.scale) &&& ((negE &&& toGEJ c) >>> Secp.scale) >>> Secp.gej_add >>> normalize
  eT=startHash "" >>> appendT r1 ctx8Add64 >>> appendT r2 ctx8Add64 >>> appendT a ctx8Add64 >>> appendT c ctx8Add64 >>> endHash >>> Secp.scalar_normalize

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
      , entryAssumptions = ["key, message, R', T and s' are witness operands", "canonical x-only key and affine coordinates <p; response s'<n; derived challenge reduced mod n"]
      , entryProgram = \w -> Prog (adaptorVerify w)
      , entryVectors =
          [ Vector ("valid pre-signature" ++ adaptorNote) env adaptorW Accept
          , Vector "same-CMR pre-signature for another message" env (let ((p, _), r) = adaptorW in ((p, toWord256 5), r)) Reject
          , Vector "same-CMR wrong adaptor point" env (let (pm, ((r', _), s')) = adaptorW in (pm, ((r', ptW (Ref.pointMul Ref.gPt 78)), s'))) Reject ]
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
      , entryAssumptions = ["ring of 4 canonical x-only keys <p (even y); e_{i+1} = sha256(m || x(R_i) || y(R_i)) mod n", "initial challenge and all four response scalars must be <n"]
      , entryProgram = \w -> Prog (ringVerify w)
      , entryVectors =
          [ Vector "valid ring signature (signer index 2)" env ringW Accept
          , Vector "same-CMR ring signature on another message" env (let ((ps, _), sg) = ringW in ((ps, toWord256 9), sg)) Reject ]
      }
    , Entry
      { entryId = "eprint-dleq-cashu"
      , entryTitle = "Chaum-Pedersen DLEQ proof (Cashu NUT-12 style)"
      , entrySpec = "Chaum-Pedersen discrete-log equality; Cashu NUT-12 blind-signature DLEQ"
      , entryCategory = Eprint
      , entryVectorSource = Derived "proofs from Ref.Bip340 point arithmetic"
      , entryAssumptions = ["transcript: sha256(R1 || R2 || A || C) over 64-byte affine points (NUT-12 hashes hex encodings)", "canonical affine coordinates <p and challenge/response scalars <n; custom transcript challenge reduced mod n"]
      , entryProgram = \w -> Prog (dleqVerify w)
      , entryVectors =
          [ Vector "valid DLEQ proof" env dleqW Accept
          , Vector "same-CMR C from a different secret" env (let ((a, (b, _)), es) = dleqW in ((a, (b, ptW (Ref.pointMul (Just bPt) 12345))), es)) Reject ]
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

encPt (Just(x,y))=(toWord256 x,toWord256 y)
encPt Nothing=error "infinity"
encHashNum=Ref.intFromBytes.hashToBytes.sha256
encSer (Just(x,y))=Ref.bytesFromInt x<>Ref.bytesFromInt y
encSer Nothing=error "infinity"

encSmall=Ref.liftX 1

-- A valid encAdaptor relation with s'=1 and a encSmall-x public key. T is derived
-- from the relation; verifier does not demand knowledge of the encAdaptor log.
encAdaptor rawPk s=Prog (witness w >>> adaptorT)
 where
  m=0x991
  e=Ref.intFromBytes (Ref.taggedHash "BIP0340/challenge" (Ref.bytesFromInt (Ref.pubkeyOf 1)<>Ref.bytesFromInt rawPk<>Ref.bytesFromInt m)) `mod`Ref.n
  rp=Ref.pointAdd Ref.gPt (Ref.pointMul encSmall (Ref.n-e))
  t=Ref.pointAdd Ref.gPt (Ref.pointMul rp (Ref.n-1))
  w=((toWord256 rawPk,toWord256 m),((encPt rp,encPt t),toWord256 s))

-- a=1, B=C=lift_x(1). B is not in the challenge transcript, so replacing B.x
-- by p+1 leaves a valid old relation. C encoding changes are rehashed exactly.
encDleq badB badC=Prog (witness w >>> dleqT)
 where
  rr=12345
  a=Ref.gPt;b=encSmall;c=encSmall
  Just(cx,cy)=c
  cw=if badC then (toWord256 (cx+Ref.p),toWord256 cy) else encPt c
  bw=if badB then (toWord256 (cx+Ref.p),toWord256 cy) else encPt b
  r1=Ref.pointMul Ref.gPt rr;r2=Ref.pointMul b rr
  e=encHashNum (encSer r1<>encSer r2<>encSer a<>Ref.bytesFromInt (fromWord256(fst cw))<>Ref.bytesFromInt(fromWord256(snd cw))) `mod`Ref.n
  s=(rr+e) `mod`Ref.n
  w=((encPt a,(bw,cw)),(toWord256 e,toWord256 s))

encRing badKey badScalar=Prog (witness w >>> ringT)
 where
  sks=[1,222,333,444]
  evenSk sk=let Just(_,y)=Ref.pointMul Ref.gPt sk in if even y then sk else Ref.n-sk
  ds=map evenSk sks
  pks=[1,Ref.pubkeyOf(ds!!1),Ref.pubkeyOf(ds!!2),Ref.pubkeyOf(ds!!3)]
  msg=0x991
  h q=encHashNum (Ref.bytesFromInt msg<>encSer q) `mod`Ref.n
  nonce i s e=Ref.pointAdd (Ref.pointMul Ref.gPt s) (Ref.pointMul (Ref.liftX(pks!!i)) (Ref.n-e))
  k=5555;e3=h(Ref.pointMul Ref.gPt k);e0=h(nonce 3 9004 e3);e1=h(nonce 0 1 e0);e2=h(nonce 1 9002 e1)
  s2=(k+e2*(ds!!2)) `mod`Ref.n
  ps=map toWord256 (if badKey then (Ref.p+1):tail pks else pks)
  ss=map toWord256 [if badScalar then Ref.n+1 else 1,9002,s2,9004]
  w=((((ps!!0,ps!!1),(ps!!2,ps!!3)),toWord256 msg),(toWord256 e0,((ss!!0,ss!!1),(ss!!2,ss!!3))))


-- Actual before/after regression fixtures: each pair has an identical CMR.
-- The malformed encoding satisfies the raw group equations but must reject.
encodingProbes :: [(String,Prog,Prog)]
encodingProbes=
 [ ("adaptor s+n",encAdaptor 1 1,encAdaptor 1 (Ref.n+1))
 , ("adaptor noncanonical public key",encAdaptor 1 1,encAdaptor (Ref.p+1) 1)
 , ("DLEQ noncanonical B",encDleq False False,encDleq True False)
 , ("DLEQ noncanonical C",encDleq False False,encDleq False True)
 , ("ring noncanonical key",encRing False False,encRing True False)
 , ("ring s+n",encRing False False,encRing False True)]
