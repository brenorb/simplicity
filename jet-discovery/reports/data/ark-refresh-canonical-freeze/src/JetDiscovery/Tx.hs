-- | Transaction and environment builders for test vectors.
--
-- Includes a parser for raw Bitcoin transactions (with or without segwit
-- serialization) so upstream vectors that are given as transaction hex
-- (for example BIP 119's @ctvhash.json@) can be loaded directly.
module JetDiscovery.Tx
  ( -- * Hex and hashes
    unhex, hex, hashFromInteger, hashToInteger, hashFromBytes, hashToBytes, sha256, taggedSha256
    -- * Building transactions
  , dummyOutpoint, mkInput, mkOutput, mkTx, defaultTap, mkEnv
    -- * Raw transactions
  , RawTx(..), RawIn(..), RawOut(..), parseRawTx, rawToSigTx, parseTxOut, taprootAnnex
  , putCompactSize
  ) where

import Control.Monad (replicateM, when)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Lazy as BSL
import Data.Bits (shiftL, shiftR, (.&.))
import Data.Char (digitToInt, intToDigit)
import Data.Serialize (Get, Putter, runGet, getWord8, getWord16le, getWord32le, getWord64le, getByteString, putWord8, putWord16le, putWord32le, putWord64le, lookAhead, skip, remaining, put, runPut, get)
import qualified Data.Vector as V
import Data.Word (Word8, Word32, Word64)
import Lens.Family2 (review, over, view, under)

import Simplicity.Digest
import Simplicity.Bitcoin.DataTypes
import Simplicity.Bitcoin.Primitive (PrimEnv, primEnv)
import Simplicity.LibSecp256k1.Schnorr (PubKey(..))

unhex :: String -> BS.ByteString
unhex = BS.pack . go
 where
  go (a:b:r) = fromIntegral (digitToInt a * 16 + digitToInt b) : go r
  go [] = []
  go _ = error "unhex: odd length"

hex :: BS.ByteString -> String
hex = concatMap byte . BS.unpack
 where
  byte w = [intToDigit (fromIntegral w `shiftR` 4), intToDigit (fromIntegral w .&. 15)]

hashFromInteger :: Integer -> Hash256
hashFromInteger = review (over be256) . fromInteger

hashToInteger :: Hash256 -> Integer
hashToInteger = integerHash256

-- | Big-endian bytes to a hash value.
hashFromBytes :: BS.ByteString -> Hash256
hashFromBytes bs | BS.length bs == 32 = either error id (runGet get bs)
                 | otherwise = error "hashFromBytes: need 32 bytes"

hashToBytes :: Hash256 -> BS.ByteString
hashToBytes = runPut . put

sha256 :: BS.ByteString -> Hash256
sha256 = bsHash

-- | BIP 340 style tagged hash.
taggedSha256 :: String -> BS.ByteString -> Hash256
taggedSha256 tag msg = bsHash (t <> t <> msg)
 where t = hashToBytes (bsHash (BSC.pack tag))

dummyOutpoint :: Word32 -> Outpoint
dummyOutpoint n = Outpoint (hashFromInteger (0x1111 + toInteger n)) n

-- | An input spending @value@ satoshi locked by @script@.
mkInput :: Outpoint -> Value -> Script -> Word32 -> SigTxInput
mkInput op value script sq = SigTxInput
  { sigTxiPreviousOutpoint = op
  , sigTxiTxo = TxOutput value script
  , sigTxiSequence = sq
  , sigTxiAnnex = Nothing
  , sigTxiScriptSig = BSL.empty
  }

mkOutput :: Value -> BS.ByteString -> TxOutput
mkOutput v s = TxOutput v (BSL.fromStrict s)

mkTx :: Word32 -> [SigTxInput] -> [TxOutput] -> Lock -> SigTx
mkTx ver ins outs lock = SigTx ver (V.fromList ins) (V.fromList outs) lock

-- | A taproot environment for a Simplicity leaf with the given script CMR.
defaultTap :: Hash256 -> TapEnv
defaultTap cmr = TapEnv
  { tapleafVersion = 0xbe
  , tapInternalKey = PubKey 0x50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0 -- BIP 341 NUMS point
  , tappath = []
  , tapScriptCMR = cmr
  }

-- | Build the environment for spending input @ix@ of @tx@ with a given taproot environment.
mkEnv :: SigTx -> Word32 -> (Hash256 -> TapEnv) -> Hash256 -> Maybe PrimEnv
mkEnv tx ix tap cmr = primEnv tx ix (tap cmr)

-- Raw transactions --------------------------------------------------------

data RawIn = RawIn { riOutpoint :: Outpoint, riScriptSig :: BS.ByteString, riSequence :: Word32 } deriving Show
data RawOut = RawOut { roValue :: Word64, roScript :: BS.ByteString } deriving Show
data RawTx = RawTx { rtVersion :: Word32, rtIns :: [RawIn], rtOuts :: [RawOut], rtLock :: Word32
                   , rtWitness :: [[BS.ByteString]]  -- ^ one witness stack per input (empty lists for legacy transactions)
                   } deriving Show

getCompactSize :: Get Word64
getCompactSize = do
  b <- getWord8
  case b of
    0xfd -> fromIntegral <$> getWord16le
    0xfe -> fromIntegral <$> getWord32le
    0xff -> getWord64le
    _ -> return (fromIntegral b)

putCompactSize :: Putter Word64
putCompactSize n | n < 0xfd = putWord8 (fromIntegral n)
                 | n <= 0xffff = putWord8 0xfd >> putWord16le (fromIntegral n)
                 | n <= 0xffffffff = putWord8 0xfe >> putWord32le (fromIntegral n)
                 | otherwise = putWord8 0xff >> putWord64le n

getVarBytes :: Get BS.ByteString
getVarBytes = getCompactSize >>= getByteString . fromIntegral

-- | Parse a serialized transaction (legacy or BIP 144 segwit format).  Witness data is skipped.
parseRawTx :: BS.ByteString -> Either String RawTx
parseRawTx = runGet $ do
  ver <- getWord32le
  marker <- lookAhead getWord8
  segwit <- if marker == 0
            then do { skip 1; flag <- getWord8; when (flag == 0) (fail "bad flag"); return True }
            else return False
  nIn <- getCompactSize
  ins <- replicateM (fromIntegral nIn) $ do
    h <- getByteString 32
    i <- getWord32le
    ss <- getVarBytes
    sq <- getWord32le
    -- Preserve the raw32 bytes. This is the in-tree Serialize Outpoint and
    -- Bitcoin primitive API convention; explorer display strings reverse them.
    return (RawIn (Outpoint (hashFromBytes h) i) ss sq)
  nOut <- getCompactSize
  outs <- replicateM (fromIntegral nOut) $ RawOut <$> getWord64le <*> getVarBytes
  wit <- if segwit then mapM (const $ do { n <- getCompactSize; replicateM (fromIntegral n) getVarBytes }) ins
                   else return (map (const []) ins)
  lock <- getWord32le
  r <- remaining
  when (r /= 0) (fail "trailing bytes")
  return (RawTx ver ins outs lock wit)

-- | Convert a raw transaction to a 'SigTx'.  Spent outputs are not part of a
-- raw transaction, so each input spends a dummy 0-value output with an empty script.
rawToSigTx :: RawTx -> SigTx
rawToSigTx (RawTx ver ins outs lock _) = mkTx ver (map inp ins) (map out outs) lock
 where
  inp (RawIn op ss sq) = (mkInput op 0 BSL.empty sq) { sigTxiScriptSig = BSL.fromStrict ss }
  out (RawOut v s) = mkOutput v s

-- | Parse a serialized @CTxOut@ (value, script).
parseTxOut :: BS.ByteString -> Either String TxOutput
parseTxOut = runGet $ do
  v <- getWord64le
  s <- getVarBytes
  return (TxOutput v (BSL.fromStrict s))

-- | The BIP 341 annex of a witness stack, if present (last element starting with 0x50, with at least two elements).
taprootAnnex :: [BS.ByteString] -> Maybe BS.ByteString
taprootAnnex stack | length stack >= 2, Just (0x50, _) <- BS.uncons (last stack) = Just (last stack)
                   | otherwise = Nothing
