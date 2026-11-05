{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Additional published verification relations with concrete Bitcoin uses.
-- Each entry states where it is a full authorization and where it is one
-- accountability/dispute component of a larger protocol.
module JetDiscovery.Corpus.EprintExpansion (entries, blindResponseT, frostShareT) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.List as L
import Data.Bits (testBit)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Ty.Word
import qualified Simplicity.Bitcoin.Jets as Jets
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Bitcoin.Jets (unwrap)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

sha32 :: Assert term => term Word256 Word256
sha32 = ((unit >>> ctx8Init) &&& iden) >>> ctx8Add32 >>> ctx8Finalize

kw :: (Core term, TyC a) => Integer -> term a Word256
kw = konst . toWord256

type GE = (Word256, Word256)
type GEJ = (GE, Word256)

jac :: (Core term, TyC a) => term a GE -> term a GEJ
jac t = t &&& kw 1

norm :: Assert term => term GEJ GE
norm = Secp.gej_normalize >>> verify

onCurve :: (Assert term, TyC a) => term a GE -> term a ()
onCurve t = ((t >>> oh) &&& kw Ref.p >>> Arith.lt word256 >>> verify) &&&
            (((t >>> ih) &&& kw Ref.p >>> Arith.lt word256 >>> verify) &&&
             (t >>> Secp.ge_is_on_curve >>> verify)) >>> unit

scalarCanonical :: (Assert term, TyC a) => term a Word256 -> term a ()
scalarCanonical t=(t &&& kw Ref.n) >>> Arith.lt word256 >>> verify

pt :: Ref.Pt -> GE
pt (Just (x,y)) = (toWord256 x,toWord256 y)
pt Nothing = error "test point at infinity"

bitW :: Bool -> Bit
bitW False = Left ()
bitW True = Right ()

pick :: (Core term, TyC a, TyC b) => Bool -> term a b -> term (a,a) b
pick True = drop
pick False = take

-- Bit 0 is the least significant bit of a 256-bit digest.
bit256 :: Core term => Int -> term Word256 Bit
bit256 i = pick (testBit j 7) (pick (testBit j 6) (pick (testBit j 5) (pick (testBit j 4) (pick (testBit j 3) (pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden)))))))
 where j = 255-i

hInt :: Integer -> Integer
hInt = Ref.intFromBytes . hashToBytes . sha256 . Ref.bytesFromInt

-- Lamport OTS -----------------------------------------------------------------
-- The public key is fixed in the program. Only the selected 256 preimages are
-- witness data. Message is the Bitcoin transaction sig_all_hash.
lamSecret :: Int -> Bool -> Integer
lamSecret i b = hInt (0x100000 + 2*toInteger i + if b then 1 else 0)

lamport :: forall term. (Assert term, Witness term) => [Word256] -> term () Word256 -> term () ()
lamport sig message = L.foldl' (\acc i -> (acc &&& check i) >>> unit) unit [0..255]
 where
  check i = ((witness (sig !! i) >>> sha32) &&& ((message >>> bit256 i) &&& unit >>> cond (kw (hInt (lamSecret i True))) (kw (hInt (lamSecret i False))))) >>> eq >>> verify

-- BitVM commitments and gate dispute -----------------------------------------
type Opening = (Bit,Word256)

commitments :: Int -> (Integer,Integer)
commitments i = (hInt (secret i False), hInt (secret i True))

secret :: Int -> Bool -> Integer
secret i b = 0x314159265358979323846 + 2*toInteger i + if b then 1 else 0

opening :: Int -> Bool -> Opening
opening i b = (bitW b,toWord256 (secret i b))

-- Preserve the bit after verifying its fixed two-hash commitment.
opened :: forall term. Assert term => Int -> term Opening Bit
opened i = (((ih >>> sha32) &&& (oh &&& unit >>> cond (kw h1) (kw h0))) >>> eq >>> verify) &&& oh >>> ih
 where (h0,h1) = commitments i

nandGate :: (Assert term, Witness term) => (Opening,(Opening,Opening)) -> term () ()
nandGate w = witness w >>> (((oh >>> opened 0) &&& (ioh >>> opened 1) >>> and oh ih >>> not iden) &&& (iih >>> opened 2)) >>> eq >>> verify

-- A valid equivocation reveals both committed preimages for the SAME bit wire.
-- This is the slashing leaf of a BitVM connector, not a stand-alone bridge.
equivocation :: (Assert term, Witness term) => (Word256,Word256) -> term () ()
equivocation w = witness w >>> (((oh >>> sha32) &&& kw h0 >>> eq >>> verify) &&& ((ih >>> sha32) &&& kw h1 >>> eq >>> verify)) >>> unit
 where (h0,h1) = commitments 3

-- Blind Schnorr --------------------------------------------------------------
-- Chaum/Schnorr blinding: R*=R+aG+bP, e*=H(R*||P||m), e=e*+b,
-- issuer responds z=k+e*x; requester unblinds s=z+a. Check the response and
-- final BIP340 equation. Fixed even-y P; derived R* must also have even y.
type BlindW = ((Word256,Word256),((GE,Word256),(Word256,(Word256,Word256))))
blindResponse :: (Assert term,Witness term) => BlindW -> term () ()
blindResponse w=witness w >>> blindResponseT

-- Every field is a projection of ONE bound witness tuple. Reusing a Haskell
-- variable containing a witness expression does not bind those uses in Simplicity.
blindResponseT :: forall term. Assert term => term BlindW ()
blindResponseT=(canonical &&& ((onCurve r &&& onCurve p) &&& (issuer &&& (evenR &&& (challengeOk &&& final))))) >>> unit
 where
  pk=ooh
  message=oih
  r=ih >>> oh >>> oh
  z=ih >>> oh >>> ih
  alpha=ih >>> ih >>> oh
  beta=ih >>> ih >>> ih >>> oh
  blindedChallenge=ih >>> ih >>> ih >>> ih
  p=(false &&& pk) >>> Secp.decompress >>> verify
  canonical=(((pk &&& kw Ref.p) >>> Arith.lt word256 >>> verify) &&& scalarCanonical z) &&&
            (scalarCanonical alpha &&& (scalarCanonical beta &&& scalarCanonical blindedChallenge)) >>> unit
  rStar :: term BlindW GE
  rStar=((((beta &&& jac p) &&& alpha) >>> Secp.linear_combination_1) &&& r) >>> Secp.gej_ge_add >>> norm
  evenR=rStar >>> ih >>> Secp.fe_is_odd >>> not iden >>> verify
  challenge=hashWords [rStar >>> oh,pk,message] >>> Secp.scalar_normalize
  hashWords ws=(iden &&& (unit >>> ctx8InitTag "BIP0340/challenge")) >>>
               L.foldl' (>>>) iden [oh &&& ((ih &&& (oh >>> field)) >>> ctx8Add32) | field<-ws] >>> ih >>> ctx8Finalize
  challengeOk=((challenge &&& beta >>> Secp.scalar_add) &&& blindedChallenge) >>> eq >>> verify
  issuer=((((blindedChallenge >>> Secp.scalar_negate) &&& p) &&& z) &&& r) >>> Secp.linear_verify_1
  final=((((challenge >>> Secp.scalar_negate) &&& p) &&& ((z &&& alpha) >>> Secp.scalar_add)) &&& rStar) >>> Secp.linear_verify_1

-- FROST share relation -------------------------------------------------------
-- RFC9591 verify_signature_share relation only; the transcript factors are
-- explicit operands. This is not a standalone authorization policy.
type FrostW=((GE,(GE,GE)),((Word256,Word256),(Word256,Word256)))
frostShare :: (Assert term,Witness term) => FrostW -> term () ()
frostShare w=witness w >>> frostShareT

frostShareT :: forall term. Assert term => term FrostW ()
frostShareT=(canonical &&& ((onCurve d &&& (onCurve e &&& onCurve p)) &&& relation)) >>> unit
 where
  d=oh >>> oh
  e=oh >>> ih >>> oh
  p=oh >>> ih >>> ih
  rho=ih >>> oh >>> oh
  challenge=ih >>> oh >>> ih
  lambda=ih >>> ih >>> oh
  z=ih >>> ih >>> ih
  canonical=(scalarCanonical rho &&& scalarCanonical challenge) &&&
            (scalarCanonical lambda &&& scalarCanonical z) >>> unit
  -- RFC9591 permits an identity commitment share. Keep this intermediate in
  -- Jacobian form and compare group elements without affine normalization.
  rhs=(((rho &&& jac e) >>> Secp.scale) &&& d) >>> Secp.gej_ge_add
  cl=(challenge &&& lambda) >>> Secp.scalar_multiply >>> Secp.scalar_negate
  lhs=((cl &&& jac p) &&& z) >>> Secp.linear_combination_1
  relation=(lhs &&& rhs) >>> Secp.gej_equiv >>> verify

entries :: [Entry]
entries = [lamportEntry,nandEntry,equivEntry,blindEntry,frostEntry]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 99000 mempty] 0) 0 defaultTap
  env2 = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 100000 mempty 0xfffffffe] [mkOutput 98000 mempty] 0) 0 defaultTap
  lamProgram ws = Prog (lamport ws sigMsg)
  lamCmr = progCmr (lamProgram (replicate 256 (toWord256 0)))
  lamMessage = maybe (error "Lamport environment") (\e -> maybe (error "Lamport sighash") fromWord256 (Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ())) (env lamCmr)
  lamSig = [toWord256 (lamSecret i (testBit lamMessage i)) | i <- [0..255]]
  lamportEntry = Entry
    { entryId = "eprint-lamport-transaction-signature"
    , entryTitle = "Lamport SHA-256 one-time authorization over the Bitcoin transaction"
    , entrySpec = "Lamport OTS; BitVM eprint 2024/1995 bit commitments (full 256-bit transaction-message OTS)"
    , entryCategory = PostQuantum
    , entryVectorSource = Derived "512 deterministic secret/public-key pairs; select one preimage per bit of evaluated sig_all_hash"
    , entryAssumptions = ["one-time key; reusing the public key for another message is unsafe", "256-bit SHA-256 secret/preimage outputs; fixed 512-hash public key", "full transaction authorization; this is Lamport OTS, not XMSS or SLH-DSA"]
    , entryProgram = lamProgram
    , entryVectors = [Vector "valid one-time signature" env lamSig Accept,Vector "corrupted preimage" env (toWord256 0 : L.drop 1 lamSig) Reject,Vector "different transaction" env2 lamSig Reject]
    }
  nandEntry = Entry
    { entryId = "eprint-bitvm-nand-dispute"
    , entryTitle = "BitVM committed-bit NAND gate verification"
    , entrySpec = "BitVM eprint 2024/1995: hash commitments and NAND circuit dispute"
    , entryCategory = Eprint
    , entryVectorSource = Derived "all four NAND input combinations with fixed independent two-hash wire commitments"
    , entryAssumptions = ["one dispute gate with three fixed bit commitments", "SHA-256 commitment variant; transaction graph and challenge windows outside this leaf"]
    , entryProgram = \w -> Prog (nandGate w)
    , entryVectors = [Vector (show (a,b)) env (opening 0 a,(opening 1 b,opening 2 (P.not (a P.&& b)))) Accept | a <- [False,True],b <- [False,True]] ++ [Vector "false NAND output, valid commitment opening" env (opening 0 True,(opening 1 True,opening 2 True)) Reject, Vector "wrong wire preimage" env (opening 0 False,(opening 1 True,(bitW True,toWord256 0))) Reject]
    }
  equivEntry = Entry
    { entryId = "eprint-bitvm-equivocation-slash"
    , entryTitle = "BitVM bit-commitment equivocation slashing leaf"
    , entrySpec = "BitVM eprint 2024/1995: reveal both wire labels to prove equivocation"
    , entryCategory = Eprint
    , entryVectorSource = Derived "fixed independent secrets for the two commitment branches"
    , entryAssumptions = ["slashing branch in a pre-signed connector graph; both preimages are necessary", "full connector graph authorization is not modeled"]
    , entryProgram = \w -> Prog (equivocation w)
    , entryVectors = [Vector "both preimages" env (toWord256 (secret 3 False),toWord256 (secret 3 True)) Accept, Vector "one preimage repeated" env (toWord256 (secret 3 False),toWord256 (secret 3 False)) Reject]
    }
  blindEntry = Entry
    { entryId = "eprint-blind-schnorr-response"
    , entryTitle = "Blind Schnorr response and unblinded BIP340 signature verification"
    , entrySpec = "Blind Schnorr algebra; eprint 2022/1676 (concurrency-safe protocols require additional machinery)"
    , entryCategory = Eprint
    , entryVectorSource = Derived "Haskell point arithmetic: R*=R+aG+bP, e=H_BIP340(R*||P||m)+b, z=k+e*x"
    , entryAssumptions = ["single-session algebraic verification; no concurrent-security claim", "even-y x-only public key and even-y blinded nonce", "Bitcoin path: blind ecash/credential issuer-response accountability, not ordinary final-signature consensus"]
    , entryProgram = \w -> Prog (blindResponse w)
    , entryVectors = [Vector "noncanonical beta" env blindBadB Reject,Vector "same-CMR public-key splice" env blindBadPk Reject,Vector "same-CMR alpha splice" env blindBadAlpha Reject,Vector "valid issuer response and unblinding" env blindW Accept,Vector "wrong blinded challenge" env (let (pm,(rz,(a,(b,e))))=blindW in (pm,(rz,(a,(b,toWord256 (fromWord256 e+1)))))) Reject,Vector "wrong issuer response" env (let (pm,((r,z),ab))=blindW in (pm,((r,toWord256 (fromWord256 z+1)),ab))) Reject]
    }
  frostEntry = Entry
    { entryId = "eprint-frost-signature-share"
    , entryTitle = "FROST secp256k1 partial-signature accountability relation"
    , entrySpec = "RFC 9591 verify_signature_share; eprint 2020/852 FROST"
    , entryCategory = Eprint
    , entryVectorSource = Derived "independent Integer/scalar point arithmetic with z=d+rho*e+c*lambda*x modulo n"
    , entryAssumptions = ["rho, challenge and Lagrange coefficient are relation operands; transcript derivation is not included", "affine D,E,Y points validated; all scalars range-checked against n", "Bitcoin path: threshold custody share accountability; final aggregate is already a BIP340/Schnorr check"]
    , entryProgram = \w -> Prog (frostShare w)
    , entryVectors = [Vector "valid signature share" env frostW Accept,
                      Vector "corrupt share" env frostBadZ Reject,
                      Vector "wrong binding factor" env frostBadR Reject,Vector "noncanonical binding factor" env frostNoncanonical Reject,Vector "same-CMR public-share splice" env frostBadPub Reject,Vector "same-CMR hiding-commitment splice" env frostBadD Reject,
                      Vector "valid identity commitment share" env frostIdentity Accept,Vector "wrong response with identity commitment share" env frostIdentityBad Reject]
    }
  sk0 = 1234567
  Just (px,py) = Ref.pointMul Ref.gPt sk0
  sk = if even py then sk0 else Ref.n-sk0
  pp = Ref.liftX px
  a = 314159
  b = 271828
  m = 0x424242
  k = head [j | j <- [1000..], Just (_,y) <- [Ref.pointAdd (Ref.pointMul Ref.gPt (j+a)) (Ref.pointMul pp b)], even y]
  rr = Ref.pointMul Ref.gPt k
  Just (rx,_) = Ref.pointAdd (Ref.pointMul Ref.gPt (k+a)) (Ref.pointMul pp b)
  c = Ref.intFromBytes (Ref.taggedHash "BIP0340/challenge" (Ref.bytesFromInt rx <> Ref.bytesFromInt px <> Ref.bytesFromInt m)) `mod` Ref.n
  eBlind = (c+b) `mod` Ref.n
  zBlind = (k+eBlind*sk) `mod` Ref.n
  blindW = ((toWord256 px,toWord256 m),((pt rr,toWord256 zBlind),(toWord256 a,(toWord256 b,toWord256 eBlind))))
  dF=1234; eF=5678; xF=9012; rhoF=1314; cF=1516; lF=Ref.n-2
  zF=(dF+rhoF*eF+cF*lF*xF) `mod` Ref.n
  frostW = ((pt (Ref.pointMul Ref.gPt dF),(pt (Ref.pointMul Ref.gPt eF),pt (Ref.pointMul Ref.gPt xF))),((toWord256 rhoF,toWord256 cF),(toWord256 lF,toWord256 zF)))

  frostBadZ = let (dey,(rc,(l,z))) = frostW in (dey,(rc,(l,toWord256 (fromWord256 z+1))))
  frostBadR = let (dey,((r,c),lz)) = frostW in (dey,((toWord256 (fromWord256 r+1),c),lz))
  frostNoncanonical = let (dey,((r,c),lz))=frostW in (dey,((toWord256 (fromWord256 r+Ref.n),c),lz))
  blindBadB = let (pm,(rz,(a,(b,e))))=blindW in (pm,(rz,(a,(toWord256 (fromWord256 b+Ref.n),e))))
  blindBadPk=let ((_,m),rest)=blindW in ((toWord256 (Ref.pubkeyOf 42),m),rest)
  blindBadAlpha=let (pm,(rz,(a,be)))=blindW in (pm,(rz,(toWord256 (fromWord256 a+1),be)))
  frostBadPub=let ((d,(e,_)),rest)=frostW in ((d,(e,pt (Ref.pointMul Ref.gPt 42))),rest)
  frostBadD=let ((_,ep),rest)=frostW in ((pt (Ref.pointMul Ref.gPt 42),ep),rest)

  frostIdentity=((pt Ref.gPt,(pt (Ref.pointMul Ref.gPt (Ref.n-1)),pt (Ref.pointMul Ref.gPt 5))),((toWord256 1,toWord256 7),(toWord256 3,toWord256 105)))
  frostIdentityBad=let (dey,(rc,(l,_)))=frostIdentity in (dey,(rc,(l,toWord256 106)))
