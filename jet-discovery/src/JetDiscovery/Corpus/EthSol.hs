{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
-- | Popular Ethereum and Solana contract patterns, re-expressed over Bitcoin
-- UTXOs (the locked value plays the token's role):
--
-- * linear vesting (OpenZeppelin VestingWallet, Solana token-vesting);
-- * a descending-price (Dutch) auction (Seaport / Metaplex style);
-- * a 3-of-5 Safe wallet with a delegate spending allowance (Safe AllowanceModule);
-- * oracle-priced loan liquidation (Aave / Compound / Solend liquidationCall).
module JetDiscovery.Corpus.EthSol
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.List as L
import Data.Serialize (runPut, putWord64be, putWord32be)
import qualified Data.Word as DW

import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Word (shift_const_by)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Bitcoin.Primitive (PrimEnv)
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Apps (sigMsg, checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

type SigW = (Word256, Word256)
type T5 a = (a, (a, (a, (a, a))))

outValue :: (Assert term, Primitive term) => Integer -> term () Word64
outValue i = konst (w32 i) >>> primitive Prim.OutputValue >>> verify

outScript :: (Assert term, Primitive term) => Integer -> term () Word256
outScript i = konst (w32 i) >>> primitive Prim.OutputScriptHash >>> verify

sameScriptOut :: (Assert term, Primitive term) => Integer -> term () ()
sameScriptOut i = (outScript i &&& Tx.currentScriptHash) >>> eq >>> verify

to64 :: (Core term, TyC a) => term a Word32 -> term a Word64
to64 t = konst (w32 0) &&& t

-- | @t * 2^k@ with @k@ the leading zeros of a 64-bit divisor: div2n1n (the DivMod128_64
-- jet) requires a normalized divisor.
normShift :: Integer -> Int
normShift d = length (takeWhile (< 2 ^ (63 :: Int)) (iterate (* 2) d))

-- Linear vesting -----------------------------------------------------------------------

-- | vested(t) = total * (t - start) / duration, clamped to [0, total], t the transaction's
-- lock time.  The UTXO holds the unvested balance, so the beneficiary's withdrawal must
-- leave R in output 0 under this script with R * duration >= total * (start + duration - t).
vesting :: (Simplicity term, Primitive term) => Word256 -> Integer -> Integer -> Integer -> SigW -> term () ()
vesting pk total start dur sig = (checkSigWith pk sigMsg (witness sig) &&& covOk) >>> unit
 where
  left = (konst (w32 (start + dur)) &&& ((TL.txLockTime &&& konst (w32 start)) >>> Arith.max word32)) >>> Arith.subtract word32
  covOk = left >>> cond unit stays
  stays = (unit >>> sameScriptOut 0) &&& amountOk >>> unit
  amountOk = ((konst (w64 total) &&& to64 iden) >>> Arith.multiply word64) &&& ((unit >>> outValue 0) &&& konst (w64 dur) >>> Arith.multiply word64)
         >>> Arith.le word128 >>> verify

vestingRef :: Integer -> Integer -> Integer -> Integer -> Integer
vestingRef total start dur t = total - total * (P.min dur (P.max t start - start)) `div` dur

-- Dutch auction ------------------------------------------------------------------------

-- | price(t) = p0 - (p0 - floor) * min(t - t0, dur) / dur; output 0 pays the seller at least
-- price(t).  Whoever pays takes the auctioned UTXO.
dutch :: (Simplicity term, Primitive term) => Word256 -> Integer -> Integer -> Integer -> Integer -> term () ()
dutch seller p0 pf t0 dur = ((outScript 0 &&& konst seller >>> eq >>> verify) &&& payOk) >>> unit
 where
  k = normShift dur
  elapsed = ((((TL.txLockTime &&& konst (w32 t0)) >>> Arith.max word32) &&& konst (w32 t0) >>> Arith.subtract word32 >>> ih) &&& konst (w32 dur)) >>> Arith.min word32
  dividend = (konst (w64 (p0 - pf)) &&& to64 elapsed) >>> Arith.multiply word64 >>> shift_const_by false word128 k
  fall = (dividend &&& konst (w64 (dur * 2 ^ k))) >>> Arith.div2n1n word64 >>> oh
  price = (konst (w64 p0) &&& fall) >>> Arith.subtract word64 >>> ih
  payOk = (price &&& outValue 0) >>> Arith.le word64 >>> verify

dutchRef :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
dutchRef p0 pf t0 dur t = p0 - (p0 - pf) * P.min dur (P.max t t0 - t0) `div` dur

-- Safe with an allowance module -------------------------------------------------------------

at5 :: (Core term, TyC a, TyC c) => Int -> term a c -> term (T5 a) c
at5 0 t = take t
at5 1 t = drop (take t)
at5 2 t = drop (drop (take t))
at5 3 t = drop (drop (drop (take t)))
at5 _ t = drop (drop (drop (drop t)))

-- | 3 of 5 owners sign; or the delegate signs, output 0 takes at most the allowance,
-- output 1 returns the rest (less a bounded fee) to this script, and a relative timelock
-- of one period has passed (each allowance spend restarts the period, like Safe's resetTime).
safe :: (Simplicity term, Primitive term) => [Word256] -> Word256 -> Integer -> Integer -> Integer
     -> Either (T5 (Either () SigW)) SigW -> term () ()
safe owners delegate allowance period maxFee w = witness w &&& sigMsg >>> match threshold allow
 where
  slot i = (take (at5 i iden) &&& ih) >>> match (konst (w8 0)) (checkSigWith (owners !! i) ih oh >>> konst (w8 1))
  add8 a b = (a &&& b) >>> Arith.add word8 >>> ih
  count = L.foldl' (\acc i -> add8 acc (slot i)) (slot 0) [1 .. 4]
  threshold = (konst (w8 3) &&& count) >>> Arith.le word8 >>> verify
  allow = (checkSigWith delegate ih oh &&& (unit >>> allowOk)) >>> unit
  allowOk = ((outValue 0 &&& konst (w64 allowance)) >>> Arith.le word64 >>> verify)
        &&& (sameScriptOut 1 &&& (konst (w16 period) >>> TL.checkLockDistance))
        &&& (((Tx.currentValue &&& konst (w64 (allowance + maxFee))) >>> Arith.subtract word64 >>> ih) &&& outValue 1 >>> Arith.le word64 >>> verify)
        >>> unit

-- Lending liquidation ---------------------------------------------------------------------

-- | Borrower and lender close together; or anyone liquidates with an oracle price attestation
-- when collateral * price * LT < debt * 10^12 (sats, US cents per BTC, basis points, cents),
-- the attestation is at most an hour older than the lock time, and output 0 pays the lender
-- at least 95% of the collateral (a 5% liquidation bonus).
lending :: (Simplicity term, Primitive term) => Word256 -> Word256 -> Word256 -> Word256 -> Integer -> Integer
        -> Either (SigW, SigW) (Word64, (Word32, SigW)) -> term () ()
lending borrower lender lenderScript oracle debtCents ltBps w = witness w &&& sigMsg >>> match coop liq
 where
  coop = (checkSigWith borrower ih ooh &&& checkSigWith lender ih oih) >>> unit
  liq = take (oracleOk &&& freshOk &&& unhealthy &&& (unit >>> payOk)) >>> unit
  -- input (price, (ts, sig))
  attestation = (((unit >>> ctx8InitTag "Simplicity/Oracle/Price") &&& oh >>> ctx8Add8) &&& ioh >>> ctx8Add4) >>> ctx8Finalize
  oracleOk = checkSigWith oracle attestation iih
  freshOk = (ioh >>> TL.checkLockTime) &&& ((unit >>> TL.txLockTime) &&& ((ioh &&& konst (w32 3600)) >>> Arith.add word32 >>> ih) >>> Arith.le word32 >>> verify) >>> unit
  unhealthy = (((((unit >>> Tx.currentValue) &&& oh) >>> Arith.multiply word64) &&& konst (toWord128 ltBps)) >>> Arith.multiply word128)
          &&& konst (toWord256 (debtCents * 10 ^ (12 :: Int))) >>> Arith.lt word256 >>> verify
  payOk = ((outScript 0 &&& konst lenderScript) >>> eq >>> verify)
      &&& (((Tx.currentValue &&& konst (w64 9500)) >>> Arith.multiply word64) &&& ((outValue 0 &&& konst (w64 10000)) >>> Arith.multiply word64) >>> Arith.le word128 >>> verify)
      >>> unit

-- Vectors ---------------------------------------------------------------------------------

skA, skB, skC, skD, skE, skG, skO :: Integer
skA = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
skB = 0xC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9
skC = 0x0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710
skD = 0x1111111111111111111111111111111111111111111111111111111111111111
skE = 0x2222222222222222222222222222222222222222222222222222222222222222
skG = 0x3333333333333333333333333333333333333333333333333333333333333333
skO = 0x0340034003400340034003400340034003400340034003400340034003400340

pkOf :: Integer -> Word256
pkOf = w256 . Ref.pubkeyOf

sigW :: Sig -> SigW
sigW (Sig r s) = (toWord256 (toInteger r), toWord256 (toInteger s))

zeroSig :: SigW
zeroSig = (w256 0, w256 0)

-- | Spend of one input (value, script, sequence) with a lock time and outputs.
spend :: Integer -> BS.ByteString -> DW.Word32 -> DW.Word32 -> [(Integer, BS.ByteString)] -> Hash256 -> Maybe PrimEnv
spend val script sq lock outs = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) (fromInteger val) (BSL.fromStrict script) sq] [ mkOutput (fromInteger v) s | (v, s) <- outs ] lock) 0 defaultTap

signFor :: Integer -> Prog -> (Hash256 -> Maybe PrimEnv) -> SigW
signFor sk prog env = case env (progCmr prog) >>= (\e -> Jets.fastEval (unwrap (Jets.jetSubst SigHash.sigAllHash)) e ()) of
  Just m -> sigW (signMsg sk (w256ToBytes m))
  Nothing -> error "signFor"

scriptHash :: BS.ByteString -> Word256
scriptHash = w256FromBytes . hashToBytes . sha256

entries :: [Entry]
entries =
  [ Entry
    { entryId = "ethsol-linear-vesting"
    , entryTitle = "Linear vesting wallet (OpenZeppelin VestingWallet, Solana token-vesting)"
    , entrySpec = "OpenZeppelin VestingWallet.vestedAmount; the UTXO value is the unvested balance"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "expected balances from Haskell Integer arithmetic; signatures with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["time is the transaction's lock time (a time, not a height)", "total, start and duration are contract constants"]
    , entryProgram = vestProg
    , entryVectors =
        [ vv "quarter vested, 3/4 stays" (vStart + 250000) [(750000, vScript), (240000, other)] skA Accept
        , vv "quarter vested, one sat too little stays" (vStart + 250000) [(749999, vScript), (240001, other)] skA Reject
        , vv "quarter vested, remainder to another script" (vStart + 250000) [(750000, other)] skA Reject
        , vv "fully vested, everything withdrawn" (vStart + 2000000) [(990000, other)] skA Accept
        , vv "before the start, nothing withdrawn" (vStart - 5) [(1000000, vScript)] skA Accept
        , vv "before the start, one sat withdrawn" (vStart - 5) [(999999, vScript), (1, other)] skA Reject
        , vv "signed by someone else" (vStart + 250000) [(750000, vScript)] skB Reject ]
    }
  , Entry
    { entryId = "ethsol-dutch-auction"
    , entryTitle = "Descending-price (Dutch) auction"
    , entrySpec = "Linear-decay Dutch auction (Seaport descending orders, Metaplex auctions, Paradigm GDA's linear case)"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "prices from Haskell Integer arithmetic"
    , entryAssumptions = ["time is the transaction's lock time", "prices below 2^63 sats; duration below 2^32 seconds"]
    , entryProgram = \() -> dutchProg
    , entryVectors =
        [ Vector "quarter elapsed, pays exactly price" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 21600)) [(dutchRef 50000000 10000000 aStart 86400 (aStart + 21600), sellerS)]) () Accept
        , Vector "quarter elapsed, pays one sat less" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 21600)) [(dutchRef 50000000 10000000 aStart 86400 (aStart + 21600) - 1, sellerS)]) () Reject
        , Vector "odd time, pays exactly price" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 33333)) [(dutchRef 50000000 10000000 aStart 86400 (aStart + 33333), sellerS)]) () Accept
        , Vector "odd time, pays one sat less" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 33333)) [(dutchRef 50000000 10000000 aStart 86400 (aStart + 33333) - 1, sellerS)]) () Reject
        , Vector "after the end, pays the floor" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 100000)) [(10000000, sellerS)]) () Accept
        , Vector "pays a different seller" (spend 1000 aScript 0xfffffffe (fromInteger (aStart + 100000)) [(10000000, other)]) () Reject ]
    }
  , Entry
    { entryId = "ethsol-safe-allowance"
    , entryTitle = "3-of-5 Safe wallet with a delegate spending allowance"
    , entrySpec = "Safe threshold signatures plus Safe AllowanceModule (per-period spending limit for a delegate)"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "signatures with JetDiscovery.Ref.Bip340"
    , entryAssumptions = ["allowance 100000 sats per 144-block period", "fee at most 1000 sats on allowance spends"]
    , entryProgram = safeProg
    , entryVectors =
        [ Vector "owners 1, 3 and 5 sign" sEnv (Left (sigs [Just skA, Nothing, Just skC, Nothing, Just skE])) Accept
        , Vector "owners 1 and 2 sign" sEnv (Left (sigs [Just skA, Just skB, Nothing, Nothing, Nothing])) Reject
        , Vector "three signatures, one in the wrong slot" sEnv (Left (sigs [Just skA, Just skC, Just skC, Nothing, Nothing])) Reject
        , Vector "delegate spends the allowance" (aEnv 144 100000 899500) (Right (sigS skG (aEnv 144 100000 899500))) Accept
        , Vector "delegate spends one sat over" (aEnv 144 100001 899499) (Right (sigS skG (aEnv 144 100001 899499))) Reject
        , Vector "delegate spends before the period ends" (aEnv 100 100000 899500) (Right (sigS skG (aEnv 100 100000 899500))) Reject
        , Vector "delegate pays too much fee" (aEnv 144 100000 898000) (Right (sigS skG (aEnv 144 100000 898000))) Reject ]
    }
  , Entry
    { entryId = "ethsol-lending-liquidation"
    , entryTitle = "Oracle-priced loan liquidation (Aave / Compound / Solend style)"
    , entrySpec = "Aave liquidationCall health-factor test with an oracle price attestation"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "attestations and signatures with JetDiscovery.Ref.Bip340; health from Haskell Integer arithmetic"
    , entryAssumptions = [ "debt $30,000 (cents), liquidation threshold 80%, collateral is this input's value"
                         , "oracle signs tagged_hash(\"Simplicity/Oracle/Price\", price_be64 || time_be32)" ]
    , entryProgram = lendProg
    , entryVectors =
        [ Vector "borrower and lender close" (lEnv 0 [(49000000, other)]) (Left (sigL skA (lEnv 0 [(49000000, other)]), sigL skB (lEnv 0 [(49000000, other)]))) Accept
        , Vector "liquidation at $70k (unhealthy)" (lEnv (lTs + 600) [(47500000, lenderS)]) (Right (att 7000000 lTs)) Accept
        , Vector "liquidation at $100k (healthy)" (lEnv (lTs + 600) [(47500000, lenderS)]) (Right (att 10000000 lTs)) Reject
        , Vector "liquidation with a stale price" (lEnv (lTs + 3601) [(47500000, lenderS)]) (Right (att 7000000 lTs)) Reject
        , Vector "liquidation underpays the lender" (lEnv (lTs + 600) [(47499999, lenderS)]) (Right (att 7000000 lTs)) Reject
        , Vector "attestation for another price" (lEnv (lTs + 600) [(47500000, lenderS)]) (Right (let (_, r) = att 7000000 lTs in (w64 6000000, r))) Reject ]
    }
  ]
 where
  other = unhex "0014" <> BS.replicate 20 0x42
  -- vesting
  vStart = 1800000000
  vScript = unhex "5120" <> BS.replicate 32 0x31
  vestProg s = Prog (vesting (pkOf skA) 1000000 vStart 1000000 s)
  vEnv t outs = spend 1000000 vScript 0xfffffffe (fromInteger t) outs
  vv name t outs sk ex = Vector name (vEnv t outs) (signFor sk (vestProg zeroSig) (vEnv t outs)) ex
  -- auction
  aStart = 1800000000
  aScript = unhex "5120" <> BS.replicate 32 0x41
  sellerS = unhex "0014" <> BS.replicate 20 0x51
  dutchProg = Prog (dutch (scriptHash sellerS) 50000000 10000000 aStart 86400)
  -- safe
  owners = map pkOf [skA, skB, skC, skD, skE]
  sScript = unhex "5120" <> BS.replicate 32 0x61
  safeP w = Prog (safe owners (pkOf skG) 100000 144 1000 w)
  safeProg = safeP
  dummyT5 = (Left (), (Left (), (Left (), (Left (), Left ()))))
  sEnv = spend 1000000 sScript 0xfffffffe 0 [(990000, other)]
  sigS sk env = signFor sk (safeP (Right zeroSig)) env
  sigs ms = let ss = [ maybe (Left ()) (\sk -> Right (signFor sk (safeP (Left dummyT5)) sEnv)) m | m <- ms ]
            in (ss !! 0, (ss !! 1, (ss !! 2, (ss !! 3, ss !! 4))))
  aEnv sq out0 out1 = spend 1000000 sScript sq 0 [(out0, other), (out1, sScript)]
  -- lending
  lScript = unhex "5120" <> BS.replicate 32 0x71
  lenderS = unhex "0014" <> BS.replicate 20 0x72
  lTs = 1800000000
  lendP w = Prog (lending (pkOf skA) (pkOf skB) (scriptHash lenderS) (pkOf skO) 3000000 8000 w)
  lendProg = lendP
  lEnv lock outs = spend 50000000 lScript 0xfffffffe (fromInteger lock) outs
  sigL sk env = signFor sk (lendP (Left (zeroSig, zeroSig))) env
  att price ts = (w64 price, (w32 ts, sigW (signMsg skO (Ref.taggedHash "Simplicity/Oracle/Price" (runPut (putWord64be (fromInteger price) >> putWord32be (fromInteger ts)))))))
