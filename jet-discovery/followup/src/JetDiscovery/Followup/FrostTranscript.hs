{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Complete FROST(secp256k1, SHA-256) transcript verification (RFC 9591).
--
-- Unlike the frozen corpus entry @eprint-frost-signature-share@, which takes
-- the binding factor, challenge and Lagrange coefficient as operands, this
-- program derives all of them in-script from the signing transcript:
--
-- * H4(msg) and H5(encoded commitment list) with SHA-256 and the context string;
-- * both binding factors H1(PK || H4 || H5 || id), i.e. hash_to_field with
--   expand_message_xmd(SHA-256), L = 48, reduced modulo n;
-- * the group commitment R = sum (D_i + rho_i E_i), serialized compressed;
-- * the challenge H2(R || PK || msg);
-- * both Lagrange coefficients from the signer identifiers.
--
-- It then checks each signature share (RFC 9591 verify_signature_share, via
-- the measured frozen relation 'frostShareT') and the aggregate signature
-- (Appendix B: z G = R + c PK).  Policy constants are the group key and the
-- three participants' public shares of the RFC Appendix E.5 key set.
--
-- Bounds: exactly two signers out of MAX_PARTICIPANTS = 3, identifiers sorted
-- and in 1..3, a 4-byte message.  Commitments are supplied as (y parity, x),
-- so the SEC1 prefix byte is always 0x02/0x03; x must be below p and on the
-- curve.  This module is outside the frozen registered corpus (see
-- reports/FOLLOW-UP.md); it is compiled with -ifollowup/src.
module JetDiscovery.Followup.FrostTranscript
  ( entry, FrostTW, frostTranscriptT
  , refBindingFactors, refGroupCommitment, refChallenge, rfcVector, rfcExpected, makeTranscript
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Bits as Bits
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Ty.Word
import JetDiscovery.Corpus.EprintExpansion (frostShareT)
import JetDiscovery.Lib.Bytes (konst, failure)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

-- Reference (Integer) implementation ------------------------------------------

contextString :: BS.ByteString
contextString = BSC.pack "FROST-secp256k1-SHA256-v1"

h :: BS.ByteString -> BS.ByteString
h = hashToBytes . sha256

expandXmd :: BS.ByteString -> BS.ByteString -> BS.ByteString
expandXmd dst msg = BS.take 48 (b1 <> b2)
 where
  dstp = dst <> BS.singleton (fromIntegral (BS.length dst))
  b0 = h (BS.replicate 64 0 <> msg <> BS.pack [0, 48, 0] <> dstp)
  b1 = h (b0 <> BS.singleton 1 <> dstp)
  b2 = h (BS.pack (BS.zipWith Bits.xor b0 b1) <> BS.singleton 2 <> dstp)

hashToScalar :: String -> BS.ByteString -> Integer
hashToScalar tag msg = Ref.intFromBytes (expandXmd (contextString <> BSC.pack tag) msg) `mod` Ref.n

encPt :: (Integer, Integer) -> BS.ByteString
encPt (x, y) = BS.cons (if even y then 2 else 3) (Ref.bytesFromInt x)

decPt :: BS.ByteString -> (Integer, Integer)
decPt bs = case Ref.liftX (Ref.intFromBytes (BS.drop 1 bs)) of
  Just (x, y) -> (x, if (BS.head bs == 2) == even y then y else Ref.p - y)
  Nothing -> error "decPt: not on curve"

-- | (identifier, hiding commitment D, binding commitment E)
type RefCommit = (Integer, (Integer, Integer), (Integer, Integer))

encodeList :: [RefCommit] -> BS.ByteString
encodeList cs = BS.concat [ Ref.bytesFromInt i <> encPt d <> encPt e | (i, d, e) <- cs ]

refBindingFactors :: (Integer, Integer) -> BS.ByteString -> [RefCommit] -> [(Integer, Integer)]
refBindingFactors pk msg cs = [ (i, hashToScalar "rho" (prefix <> Ref.bytesFromInt i)) | (i, _, _) <- cs ]
 where prefix = encPt pk <> h (contextString <> BSC.pack "msg" <> msg)
                         <> h (contextString <> BSC.pack "com" <> encodeList cs)

refGroupCommitment :: (Integer, Integer) -> BS.ByteString -> [RefCommit] -> Maybe (Integer, Integer)
refGroupCommitment pk msg cs = foldl add Nothing
  [ Ref.pointAdd (Just d) (Ref.pointMul (Just e) rho) | ((_, d, e), (_, rho)) <- zip cs (refBindingFactors pk msg cs) ]
 where add acc q = Ref.pointAdd acc q

refChallenge :: (Integer, Integer) -> (Integer, Integer) -> BS.ByteString -> Integer
refChallenge r pk msg = hashToScalar "chal" (encPt r <> encPt pk <> msg)

lagrange :: Integer -> [Integer] -> Integer
lagrange i ids = (num * powMod den (Ref.n - 2)) `mod` Ref.n
 where
  num = product [ j | j <- ids, j /= i ] `mod` Ref.n
  den = product [ (j - i) `mod` Ref.n | j <- ids, j /= i ] `mod` Ref.n

powMod :: Integer -> Integer -> Integer
powMod _ 0 = 1
powMod b e = let r = powMod (b * b `mod` Ref.n) (e `div` 2) in if odd e then r * b `mod` Ref.n else r

-- RFC 9591 Appendix E.5 ----------------------------------------------------------

hexInt :: String -> Integer
hexInt = read . ("0x" ++)

hexBytes :: String -> BS.ByteString
hexBytes [] = BS.empty
hexBytes (a:b:rest) = BS.cons (fromIntegral (hexInt [a, b])) (hexBytes rest)
hexBytes _ = error "hexBytes"

groupPk :: (Integer, Integer)
groupPk = decPt (hexBytes "02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f64663b0eae87d87b4f")

participantShares :: [Integer]
participantShares = map hexInt
  [ "08f89ffe80ac94dcb920c26f3f46140bfc7f95b493f8310f5fc1ea2b01f4254c"
  , "04f0feac2edcedc6ce1253b7fab8c86b856a797f44d83d82a385554e6e401984"
  , "00e95d59dd0d46b0e303e500b62b7ccb0e555d49f5b849f5e748c071da8c0dbc" ]

publicShares :: [(Integer, Integer)]
publicShares = [ p | Just p <- map (Ref.pointMul Ref.gPt) participantShares ]

-- | RFC E.5 signing transcript: message, sorted commitments, signature shares.
rfcVector :: (BS.ByteString, [RefCommit], [Integer])
rfcVector =
  ( BSC.pack "test"
  , [ (1, decPt (hexBytes "03c699af97d26bb4d3f05232ec5e1938c12f1e6ae97643c8f8f11c9820303f1904")
        , decPt (hexBytes "02fa2aaccd51b948c9dc1a325d77226e98a5a3fe65fe9ba213761a60123040a45e"))
    , (3, decPt (hexBytes "03077507ba327fc074d2793955ef3410ee3f03b82b4cdc2370f71d865beb926ef6")
        , decPt (hexBytes "02ad53031ddfbbacfc5fbda3d3b0c2445c8e3e99cbc4ca2db2aa283fa68525b135")) ]
  , map hexInt [ "c4fce1775a1e141fb579944166eab0d65eefe7b98d480a569bbbfcb14f91c197"
               , "0160fd0d388932f4826d2ebcd6b9eaba734f7c71cf25b4279a4ca2581e47b18d" ] )

-- | Published binding factors and final signature (R encoding, z) of E.5.
rfcExpected :: ([Integer], BS.ByteString, Integer)
rfcExpected =
  ( map hexInt [ "3e08fe561e075c653cbfd46908a10e7637c70c74f0a77d5fd45d1a750c739ec6"
               , "93f79041bb3fd266105be251adaeb5fd7f8b104fb554a4ba9a0becea48ddbfd7" ]
  , hexBytes "0205b6d04d3774c8929413e3c76024d54149c372d57aae62574ed74319b5ea14d0"
  , hexInt "c65dde8492a7471437e6c2fe3da49b90d23f642b5c6dbe7e36089f096dd97324" )

-- | Sign with two of the three RFC shares, deterministic nonces (test only).
makeTranscript :: BS.ByteString -> (Integer, Integer) -> (BS.ByteString, [RefCommit], [Integer])
makeTranscript msg (ia, ib) = (msg, cs, zs)
 where
  ids = [ia, ib]
  nonces = [ (1000 + 17 * i, 2000 + 31 * i) | i <- ids ]
  cs = [ (i, pt (Ref.pointMul Ref.gPt d), pt (Ref.pointMul Ref.gPt e)) | (i, (d, e)) <- zip ids nonces ]
  rhos = map snd (refBindingFactors groupPk msg cs)
  Just r = refGroupCommitment groupPk msg cs
  c = refChallenge r groupPk msg
  zs = [ (d + e * rho + lagrange i ids * (participantShares !! fromIntegral (i - 1)) * c) `mod` Ref.n
       | (i, (d, e), rho) <- zip3 ids nonces rhos ]
  pt (Just q) = q
  pt Nothing = error "nonce at infinity"

-- Simplicity program ---------------------------------------------------------------

type GE = (Word256, Word256)
type GEJ = (GE, Word256)
type Pt33 = (Bit, Word256)
type Commit = (Word256, (Pt33, Pt33))
-- | (message, ((commitment a, commitment b), (z a, z b)))
type FrostTW = (Word32, ((Commit, Commit), (Word256, Word256)))

kw :: (Core term, TyC a) => Integer -> term a Word256
kw = konst . toWord256

geK :: (Core term, TyC a) => (Integer, Integer) -> term a GE
geK (x, y) = kw x &&& kw y

jac :: (Core term, TyC a) => term a GE -> term a GEJ
jac t = t &&& kw 1

-- | Append constant bytes, in the largest available chunks.
addConst :: forall term. Assert term => [Integer] -> term Ctx8 Ctx8
addConst [] = iden
addConst xs
  | n >= 32 = chunk 32 (konst . toWord256) ctx8Add32
  | n >= 16 = chunk 16 (konst . toWord128) ctx8Add16
  | n >= 8 = chunk 8 (konst . toWord64) ctx8Add8
  | n >= 4 = chunk 4 (konst . toWord32) ctx8Add4
  | n >= 2 = chunk 2 (konst . toWord16) ctx8Add2
  | otherwise = chunk 1 (konst . toWord8) ctx8Add1
 where
  n = length xs
  be = P.foldl (\a b -> a * 256 + b) 0
  chunk :: TyC w => Int -> (Integer -> term Ctx8 w) -> term (Ctx8, w) Ctx8 -> term Ctx8 Ctx8
  chunk k mk add = (iden &&& mk (be (P.take k xs))) >>> add >>> addConst (P.drop k xs)

bytesOf :: BS.ByteString -> [Integer]
bytesOf = map fromIntegral . BS.unpack

-- | Append a compressed point (0x02 + parity, x).
addPt :: Assert term => term (Ctx8, Pt33) Ctx8
addPt = ((oh &&& (ioh &&& unit >>> cond (konst (toWord8 3)) (konst (toWord8 2)))) >>> ctx8Add1) &&& iih >>> ctx8Add32

-- | hash_to_field(msg, 1) with expand_message_xmd(SHA-256), L = 48, modulo n.
-- 'adder' appends msg to a context that already holds Z_pad.
xmdScalar :: forall term i. (Assert term, TyC i) => String -> term (Ctx8, i) Ctx8 -> term i Word256
xmdScalar tag adder = b0 >>> (iden &&& b1) >>> ((ih &&& b2) >>> reduce)
 where
  dst = bytesOf contextString ++ map (toInteger . fromEnum) tag
  dstp = dst ++ [toInteger (length dst)]
  start = unit >>> ctx8Init >>> addConst (replicate 64 0)
  b0 = (start &&& iden) >>> adder >>> addConst ([0, 48, 0] ++ dstp) >>> ctx8Finalize
  b1 = ((unit >>> ctx8Init) &&& iden) >>> ctx8Add32 >>> addConst (1 : dstp) >>> ctx8Finalize
  -- input (b0, b1): b2 = H((b0 xor b1) || 0x02 || DST')
  b2 = ((unit >>> ctx8Init) &&& W.bitwise_xor word256) >>> ctx8Add32 >>> addConst (2 : dstp) >>> ctx8Finalize
  -- input (b1, b2): the 48 uniform bytes are b1 || b2[0..15], i.e.
  -- hi * 2^256 + lo with hi = b1[0..15] and lo = b1[16..31] || b2[0..15].
  reduce = (((oh >>> ih) &&& (ih >>> oh)) >>> Secp.scalar_normalize) &&&
           (((konst (toWord128 0) &&& (oh >>> oh)) &&& kw c256) >>> Secp.scalar_multiply) >>> Secp.scalar_add
  c256 = 2 ^ (256 :: Int) `mod` Ref.n

someOrFail :: (Assert term, TyC a) => term (Either () a) a
someOrFail = (iden &&& unit) >>> match failure oh

-- | Validated SEC1 decompression: x < p and on the curve.
dec :: Assert term => term Pt33 GE
dec = (((ih &&& kw Ref.p) >>> Arith.lt word256 >>> verify) &&& (Secp.decompress >>> someOrFail)) >>> ih

-- | Append the 32-byte identifier, then D and E compressed.
addCommit :: Assert term => term (Ctx8, Commit) Ctx8
addCommit = (((oh &&& ioh) >>> ctx8Add32) &&& iih) >>> (((oh &&& ioh) >>> addPt) &&& iih) >>> addPt

frostTranscriptT :: forall term. Assert term => term FrostTW ()
frostTranscriptT = s1 >>> s2 >>> s3 >>> s4 >>> s5 >>> s6 >>> checks
 where
  pkBytes = bytesOf (encPt groupPk)
  ctxBytes tag = bytesOf contextString ++ map (toInteger . fromEnum) tag
  -- E0 = FrostTW
  msgT = oh
  caT = ih >>> oh >>> oh
  cbT = ih >>> oh >>> ih
  -- E1 = (E0, (H4, H5))
  h4 = ((unit >>> ctx8Init >>> addConst (ctxBytes "msg")) &&& msgT) >>> ctx8Add4 >>> ctx8Finalize
  h5 = ((((unit >>> ctx8Init >>> addConst (ctxBytes "com")) &&& caT) >>> addCommit) &&& cbT) >>> addCommit >>> ctx8Finalize
  s1 = iden &&& (h4 &&& h5)
  -- E2 = (E1, (rho a, rho b)); binding factor input PK || H4 || H5 || id
  rho c = xmdScalar "rho" (r1 >>> r2 >>> r3 >>> r4)
   where
    r1 = (oh >>> addConst pkBytes) &&& ih
    r2 = ((oh &&& (ih >>> ih >>> oh)) >>> ctx8Add32) &&& ih
    r3 = ((oh &&& (ih >>> ih >>> ih)) >>> ctx8Add32) &&& ih
    r4 = (oh &&& (ih >>> oh >>> c >>> oh)) >>> ctx8Add32
  s2 = iden &&& (rho caT &&& rho cbT)
  -- E3 = (E2, ((D a, E a), (D b, E b)))
  e0of2 = oh >>> oh
  s3 = iden &&& (((e0of2 >>> caT >>> ih >>> oh >>> dec) &&& (e0of2 >>> caT >>> ih >>> ih >>> dec)) &&&
                 ((e0of2 >>> cbT >>> ih >>> oh >>> dec) &&& (e0of2 >>> cbT >>> ih >>> ih >>> dec)))
  -- E4 = (E3, R) with R = (D a + rho a E a) + (D b + rho b E b), not the identity
  rhoA3 = oh >>> ih >>> oh
  rhoB3 = oh >>> ih >>> ih
  term3 rhoS ptsS = (((rhoS &&& jac (ptsS >>> ih)) >>> Secp.scale) &&& (ptsS >>> oh)) >>> Secp.gej_ge_add
  rJ = (term3 rhoA3 (ih >>> oh) &&& term3 rhoB3 (ih >>> ih)) >>> Secp.gej_add
  s4 = iden &&& (rJ >>> Secp.gej_normalize >>> someOrFail)
  -- E5 = (E4, c), c = H2(R || PK || msg)
  rEnc = (ih >>> Secp.fe_is_odd) &&& oh
  c1 = ((oh &&& (ih >>> ih >>> rEnc)) >>> addPt) &&& ih
  c2 = (oh >>> addConst pkBytes) &&& ih
  c3 = (oh &&& (ih >>> oh >>> oh >>> oh >>> oh >>> msgT)) >>> ctx8Add4
  s5 = iden &&& xmdScalar "chal" (c1 >>> c2 >>> c3)
  -- E6 = (E5, (lambda a, lambda b)) for identifiers xa < xb:
  -- lambda a = xb / (xb - xa), lambda b = -xa / (xb - xa)
  e0of5 = oh >>> oh >>> oh >>> oh >>> oh
  xa5 = e0of5 >>> caT >>> oh
  xb5 = e0of5 >>> cbT >>> oh
  inv5 = (xb5 &&& (xa5 >>> Secp.scalar_negate)) >>> Secp.scalar_add >>> Secp.scalar_invert
  lambdas = ((xa5 &&& xb5) &&& inv5) >>>
            (((oih &&& ih) >>> Secp.scalar_multiply) &&& (((ooh &&& ih) >>> Secp.scalar_multiply) >>> Secp.scalar_negate))
  s6 = iden &&& lambdas
  -- final checks on E6
  e5 = oh
  e4 = e5 >>> oh
  e3 = e4 >>> oh
  e2 = e3 >>> oh
  e0 = e2 >>> oh >>> oh
  pts = e3 >>> ih
  xa = e0 >>> caT >>> oh
  xb = e0 >>> cbT >>> oh
  lt t u = (t &&& u) >>> Arith.lt word256
  idsOk = and (lt (kw 0) xa) (and (lt xa xb) (lt xb (kw 4))) >>> verify
  pubOf x = ((x &&& kw 1) >>> eq) &&& iden >>> cond (geK (publicShares !! 0))
              (((x &&& kw 2) >>> eq) &&& iden >>> cond (geK (publicShares !! 1)) (geK (publicShares !! 2)))
  challenge = e5 >>> ih
  share dS eS x rhoS lamS zS = ((dS &&& (eS &&& pubOf x)) &&& ((rhoS &&& challenge) &&& (lamS &&& zS))) >>> frostShareT
  shareA = share (pts >>> oh >>> oh) (pts >>> oh >>> ih) xa (e2 >>> ih >>> oh) (ih >>> oh) (e0 >>> ih >>> ih >>> oh)
  shareB = share (pts >>> ih >>> oh) (pts >>> ih >>> ih) xb (e2 >>> ih >>> ih) (ih >>> ih) (e0 >>> ih >>> ih >>> ih)
  zSum = (e0 >>> ih >>> ih) >>> Secp.scalar_add
  aggregate = ((((challenge >>> Secp.scalar_negate) &&& jac (geK groupPk)) &&& zSum) >>> Secp.linear_combination_1)
              &&& jac (e4 >>> ih) >>> Secp.gej_equiv >>> verify
  checks = (idsOk &&& (shareA &&& (shareB &&& aggregate))) >>> unit

-- Corpus entry --------------------------------------------------------------------

witnessOf :: (BS.ByteString, [RefCommit], [Integer]) -> FrostTW
witnessOf (msg, [ca, cb], [za, zb]) = (toWord32 (Ref.intFromBytes msg), ((commit ca, commit cb), (toWord256 za, toWord256 zb)))
 where
  commit (i, d, e) = (toWord256 i, (pt33 d, pt33 e))
  pt33 (x, y) = (if odd y then Right () else Left (), toWord256 x)
witnessOf _ = error "two signers"

entry :: Entry
entry = Entry
  { entryId = "followup-frost-secp256k1-transcript"
  , entryTitle = "FROST(secp256k1, SHA-256) two-of-three complete transcript and aggregate verification"
  , entrySpec = "RFC 9591 sections 4.4-4.6, 5.3, 6.5 and Appendix B; eprint 2020/852 FROST"
  , entryCategory = Eprint
  , entryVectorSource = Upstream "vendor-specs/eprint/rfc9591.txt Appendix E.5, plus derived signing sets"
  , entryAssumptions =
      [ "policy constants: RFC E.5 group key and the three participants' public shares"
      , "exactly two signers, identifiers sorted in 1..3; message bounded to 4 bytes"
      , "binding factors, group commitment, challenge and Lagrange coefficients derived in-script"
      , "commitments supplied as (y parity, x); x < p and on-curve checked; R must not be the identity" ]
  , entryProgram = \w -> Prog (witness w >>> frostTranscriptT)
  , entryVectors =
      [ Vector "RFC 9591 E.5 transcript, signers 1 and 3" env rfc Accept
      , Vector "derived transcript, signers 1 and 2" env (witnessOf (makeTranscript (BSC.pack "test") (1, 2))) Accept
      , Vector "derived transcript, signers 2 and 3, other message" env (witnessOf (makeTranscript (BSC.pack "spnd") (2, 3))) Accept
      , Vector "share a plus one" env (bumpZ True rfc) Reject
      , Vector "share b plus one" env (bumpZ False rfc) Reject
      , Vector "shares swapped" env (swapZ rfc) Reject
      , Vector "message changed" env (setMsg (BSC.pack "tesT") rfc) Reject
      , Vector "hiding commitment a negated" env (flipD rfc) Reject
      , Vector "commitments out of order" env (swapCommits rfc) Reject
      , Vector "identifier 4" env (withId 4 rfc) Reject
      , Vector "identifier 0" env (withIdA 0 rfc) Reject
      , Vector "x not below p" env (withDx Ref.p rfc) Reject
      , Vector "x not on the curve" env (withDx offCurveX rfc) Reject
      , Vector "signer 2 transcript checked against signer 3 key" env (relabel (makeTranscript (BSC.pack "test") (1, 2))) Reject ]
  }
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  rfc = witnessOf rfcVector
  plus1 z = toWord256 ((fromWord256 z + 1) `mod` Ref.n)
  bumpZ a (m, (cs, (za, zb))) = (m, (cs, if a then (plus1 za, zb) else (za, plus1 zb)))
  swapZ (m, (cs, (za, zb))) = (m, (cs, (zb, za)))
  setMsg bs (_, rest) = (toWord32 (Ref.intFromBytes bs), rest)
  flipD (m, (((i, ((par, x), e)), cb), zs)) = (m, (((i, ((flipBit par, x), e)), cb), zs))
  flipBit (Left ()) = Right ()
  flipBit (Right ()) = Left ()
  swapCommits (m, ((ca, cb), (za, zb))) = (m, ((cb, ca), (zb, za)))
  withId k (m, ((ca, (_, pe)), zs)) = (m, ((ca, (toWord256 k, pe)), zs))
  withIdA k (m, (((_, pe), cb), zs)) = (m, (((toWord256 k, pe), cb), zs))
  withDx x (m, (((i, ((par, _), e)), cb), zs)) = (m, (((i, ((par, toWord256 x), e)), cb), zs))
  relabel w = withId 3 (witnessOf' w)
  witnessOf' = witnessOf
  offCurveX = head [ x | x <- [5 ..], Ref.liftX x == Nothing ]
