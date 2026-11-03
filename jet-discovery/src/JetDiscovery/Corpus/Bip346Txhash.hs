{-# LANGUAGE ScopedTypeVariables #-}
-- | BIP 346 OP_TXHASH.
--
-- TXHASH hashes, per selected item, SHA-256 of scriptSigs and scriptPubKeys
-- and of annexes without a length prefix: exactly the per-item hashes Bitcoin
-- Simplicity's introspection jets return.  So unlike BIP 119 and BIP 446,
-- TXHASH needs no witness re-serialization.
--
-- The TxFieldSelector is decoded in Haskell (in a script it is usually a
-- constant), into flags and two 16-bit selection masks (BIP 346 requires
-- strictly increasing indices, so a mask is exact).  The program then hashes
-- the selected fields with the introspection jets.  Selectors that ask for
-- tapscript-only fields (control block, spent script, last OP_CODESEPARATOR
-- position) do not apply to a Simplicity spend and are skipped.
module JetDiscovery.Corpus.Bip346Txhash
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Bits ((.&.), (.|.), testBit, shiftL, shiftR)
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Word as DW
import Data.Serialize (runPut, Put)
import qualified Data.Serialize

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Tx
import JetDiscovery.Types

maxItems :: Int
maxItems = 16

-- | Decoded selector: (control bytes or empty, global flags, in/out flags, (commit #in, input mask), (commit #out, output mask)).
type Sel = (BS.ByteString, (DW.Word8, DW.Word8), ((Bool, DW.Word16), (Bool, DW.Word16)))

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

bit8 :: Core term => Int -> term Word8 Bit
bit8 k = pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden)) where p = 7 - k

bit16 :: Core term => Int -> term Word16 Bit
bit16 k = pick (testBit p 3) (pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden))) where p = 15 - k

-- | Reverse the bytes of a 256-bit word (txids are hashed in wire order).
rev256 :: Core term => term Word256 Word256
rev256 = drop r128 &&& take r128
 where
  r128 = drop r64 &&& take r64
  r64 = drop bswap32 &&& take bswap32

-- | If bit b holds, apply t to the context.
when' :: (Core term, TyC c) => term () Bit -> term c c -> term c c
when' b t = (unit >>> b) &&& iden >>> cond t iden

emptyHash :: Integer
emptyHash = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

-- | The tapscript context of the current input, as operands: (sha256(control block), (sha256(leaf version || ser_string(script)), last OP_CODESEPARATOR position)).
type TapCtx = (Word256, (Word256, Word32))

txHashProg :: forall term. (Assert term, Primitive term, Witness term) => ((Buffer63 Word8, ((Word8, Word8), ((Bit, Word16), (Bit, Word16)))), TapCtx) -> Word256 -> term () ()
txHashProg ((ctl, ((g, io), ((ci, mi), (co, mo)))), (cbH, (ssH, csPos))) expected = template &&& witness expected >>> eq >>> verify
 where
  gb k = witness g >>> bit8 k
  fb k = witness io >>> bit8 k
  -- add sha256(items of the selected in/outputs) to the context, when the flag is set and the selection is not empty
  field :: term () Bit -> term () Word16 -> (Int -> term Ctx8 Ctx8) -> term Ctx8 Ctx8
  field flag mask item = when' (and flag nonEmpty) (ctxWith sub ctx8Add32)
   where
    nonEmpty = mask >>> (iden &&& konst (w16 0) >>> eq) >>> not iden
    sub = ctx8Init >>> foldr (\j k -> when' (mask >>> bit16 j) (item j) >>> k) iden [0 .. maxItems - 1] >>> ctx8Finalize
  inp j p = konst (w32 (toInteger j)) >>> primitive p
  -- each item: the input/output exists when it is selected (BIP 346 validates the indices)
  prevoutItem j = (iden &&& (unit >>> inp j Prim.InputPrevOutpoint >>> verify)) >>> ((oh &&& drop (take rev256) >>> ctx8Add32) &&& iih) >>> ctxAddLE32
  seqItem j = ctxWith (inp j Prim.InputSequence >>> verify) ctxAddLE32
  ssItem j = ctxWith (inp j Prim.InputScriptSigHash >>> verify) ctx8Add32
  spkItem j = ctxWith (inp j Prim.InputScriptHash >>> verify) ctx8Add32
  valItem j = ctxWith (inp j Prim.InputValue >>> verify) ctxAddLE64
  annexItem j = ctxWith (((inp j Prim.InputAnnexHash >>> verify) &&& unit) >>> match (konst (toWord256 emptyHash)) oh) ctx8Add32
  outSpk j = ctxWith (inp j Prim.OutputScriptHash >>> verify) ctx8Add32
  outVal j = ctxWith (inp j Prim.OutputValue >>> verify) ctxAddLE64
  template = ctx8Init
         >>> when' (gb 7) (ctxWith (witness ctl) (ctx8AddBuffer buffer63))
         >>> when' (gb 0) (ctxWith (primitive Prim.Version) ctxAddLE32)
         >>> when' (gb 1) (ctxWith (primitive Prim.LockTime) ctxAddLE32)
         >>> when' (gb 2) (ctxWith (primitive Prim.CurrentIndex) ctxAddLE32)
         >>> when' (gb 3) (ctxWith (witness cbH) ctx8Add32)
         >>> when' (gb 4) (ctxWith (witness ssH) ctx8Add32)
         >>> when' (gb 5) (ctxWith (witness csPos) ctxAddLE32)
         >>> when' (gb 6) (ctxWith ((Tx.currentAnnexHash &&& unit) >>> match (konst (toWord256 emptyHash)) oh) ctx8Add32)
         >>> when' (witness ci) (ctxWith Tx.numInputs ctxAddLE32)
         >>> field (fb 0) (witness mi) prevoutItem
         >>> field (fb 1) (witness mi) seqItem
         >>> field (fb 2) (witness mi) ssItem
         >>> field (fb 3) (witness mi) spkItem
         >>> field (fb 4) (witness mi) valItem
         >>> field (fb 5) (witness mi) annexItem
         >>> when' (witness co) (ctxWith Tx.numOutputs ctxAddLE32)
         >>> field (fb 6) (witness mo) outSpk
         >>> field (fb 7) (witness mo) outVal
         >>> ctx8Finalize

-- Selector decoding (transcribed from vendor-specs/bips/bip-0346_ref-impl_src_main.rs) ------------

convertShort :: DW.Word8 -> Maybe [DW.Word8]
convertShort t = do
  is <- case t .&. 3 of { 0 -> Just 0x00; 1 -> Just 0x40; 3 -> Just 0x3f; _ -> Nothing }
  os <- case t .&. 12 of { 0 -> Just 0x00; 4 -> Just 0x40; 12 -> Just 0x3f; _ -> Nothing }
  let base0 = 0x01 .|. 0x02 .|. 0x80 .|. 0x40
      io0 = 0xc0 .|. 0x02 .|. 0x04
      io1 = if testBit t 4 then io0 .|. 0x01 else io0
      io2 = if testBit t 5 then io1 .|. 0x08 .|. 0x10 else io1
      base1 = if testBit t 6 then base0 .|. 0x08 .|. 0x10 .|. 0x20 else base0
      base2 = if testBit t 7 then base1 .|. 0x04 else base1
  return [base2, io2, is, os]

parseSel :: DW.Word8 -> [DW.Word8] -> Int -> Int -> Maybe ([Int], Bool, [DW.Word8])
parseSel first rest nItems cur
  | sel == 0x00 = Just ([], commit, rest)
  | sel == 0x3f = Just ([0 .. nItems - 1], commit, rest)
  | sel == 0x40 = if cur >= nItems then Nothing else Just ([cur], commit, rest)
  | sel .&. 0x40 == 0 = do
      (count, rest') <- if sel .&. 0x20 == 0 then Just (fromIntegral (sel .&. 0x1f), rest)
                        else case rest of { (b:r) -> Just (fromIntegral (sel .&. 0x1f) `shiftL` 8 + fromIntegral b, r); [] -> Nothing }
      if count > nItems then Nothing else Just ([0 .. count - 1], commit, rest')
  | otherwise = individual (fromIntegral (sel .&. 0x1f)) rest []
 where
  commit = first .&. 0x80 /= 0
  sel = first .&. 0x7f
  absolute = sel .&. 0x20 == 0
  individual :: Int -> [DW.Word8] -> [Int] -> Maybe ([Int], Bool, [DW.Word8])
  individual 0 r acc = Just (reverse acc, commit, r)
  individual n (b:r) acc
    | b .&. 0x80 == 0 = place (fromIntegral b) True r
    | otherwise = case r of { (b2:r') -> place ((fromIntegral (b .&. 0x80) `shiftL` 8) + fromIntegral b2) False r'; [] -> Nothing }
   where
    place num single r' = do
      let idx | absolute = num
              | otherwise = cur + (if single then i7 num else i15 num)
      if idx < 0 || idx >= nItems || (case acc of { (l:_) -> idx <= l; [] -> False }) then Nothing else individual (n - 1) r' (idx : acc)
  individual _ [] _ = Nothing
  i7 x = let m = x .&. 0x7f in if m .&. 0x40 == 0 then m else m - 0x80
  i15 x = let m = x .&. 0x7fff in if m .&. 0x4000 == 0 then m else m - 0x8000

decode :: BS.ByteString -> Int -> Int -> Int -> Maybe Sel
decode txfs0 nIn nOut cur = do
  bytes <- case BS.unpack txfs0 of
    [] -> Just [0x07, 0xc6, 0xbf, 0xbf]  -- TXFS_SPECIAL_TEMPLATE
    [t] -> convertShort t
    bs -> Just bs
  let (global:rest0) = bytes
      (inout, rest1) = case rest0 of { (b:r) -> (b, r); [] -> (0, []) }
  (ins, ci, rest2) <- case rest1 of { (b:r) -> parseSel b r nIn cur; [] -> Just ([], False, []) }
  (outs, co, rest3) <- case rest2 of { (b:r) -> parseSel b r nOut cur; [] -> Just ([], False, []) }
  if null rest3 == False then Nothing else Just
    (if global .&. 0x80 /= 0 then BS.pack bytes else BS.empty, (global, inout), ((ci, mask ins), (co, mask outs)))
 where mask = foldr (\i m -> m .|. (1 `shiftL` i)) 0

-- Vectors ---------------------------------------------------------------------------

runPutBS :: Data.Serialize.Put -> BS.ByteString
runPutBS = runPut

entries :: IO [Entry]
entries = do
  s <- readFile "vendor-specs/bips/bip-0346_ref-impl_txhash_vectors.json"
  let txHex = strField "\"tx\"" s
      prevs = arrField "\"prevs\"" s
      Right raw = parseRawTx (unhex txHex)
      spent = [ t | Right t <- map (parseTxOut . unhex) prevs ]
      isP2tr o = BSL.length (txoScript o) == 34 && BSL.take 2 (txoScript o) == BSL.pack [0x51, 0x20]
      sigTx = (rawToSigTx raw) { sigTxIn = V.fromList [ SigTxInput op o sq (if isP2tr o then BSL.fromStrict <$> taprootAnnex w else Nothing) (BSL.fromStrict ss)
                                                      | (RawIn op ss sq, o, w) <- zip3 (rtIns raw) spent (rtWitness raw) ] }
      vecs = objects (arrRaw "\"vectors\"" s)
      nIn = length (rtIns raw)
      nOut = length (rtOuts raw)
      decoded = [ (field' "id" o, cur, (sel, cs), field' "txhash" o)
                | o <- vecs, let cur = read (rawField "input" o) :: Int
                , let csRaw = rawField "codeseparator" o
                , let cs = if csRaw == "null" then 0xffffffff else read csRaw :: Integer
                , Just sel <- [decode (unhex (field' "txfs" o)) nIn nOut cur] ]
      usable = decoded
      skipped = length vecs - length usable
      -- tapscript context of input cur from its witness: [..., script, control block (, annex)]
      tapCtx cur cs = let w = rtWitness raw !! cur
                          w' = maybe w (const (L.init w)) (taprootAnnex w)
                      in if length w' >= 2
                         then let cb = last w'; sc = last (L.init w')
                                  ser = BS.pack [BS.head cb .&. 0xfe] <> runPutBS (putCompactSize (fromIntegral (BS.length sc))) <> sc
                                  -- as rust-bitcoin: the leaf script is only defined for a well-formed control block
                                  validCb = BS.length cb >= 33 && (BS.length cb - 33) `mod` 32 == 0
                              in (w256FromBytes (hashToBytes (sha256 cb)), (if validCb then w256FromBytes (hashToBytes (sha256 ser)) else toWord256 emptyHash, w32 cs))
                         else (toWord256 emptyHash, (toWord256 emptyHash, w32 cs))
      toW (ctl, (g, io), ((ci, mi), (co, mo))) = (buffer63FromBytes ctl, ((w8 (toInteger g), w8 (toInteger io)), ((bitOf ci, w16 (toInteger mi)), (bitOf co, w16 (toInteger mo)))))
      bitOf b = if b then Right () else Left ()
      vec (i, cur, (sel, cs), h) = Vector ("txhash_vectors.json " ++ i) (mkEnv sigTx (fromIntegral cur) defaultTap) ((toW sel, tapCtx cur cs), w256FromBytes (unhex h)) Accept
      neg = case usable of
        ((i, cur, (sel, cs), h):_) -> [Vector "wrong expected hash" (mkEnv sigTx (fromIntegral cur) defaultTap) ((toW sel, tapCtx cur cs), w256 1) Reject]
        [] -> []
  return
    [ Entry
      { entryId = "bip346-txhash"
      , entryTitle = "OP_TXHASH with decoded TxFieldSelectors"
      , entrySpec = "BIP 346 (vendor-specs/bips/bip-0346.md); hashing order transcribed from its reference implementation"
      , entryCategory = CovenantBip
      , entryVectorSource = Upstream ("vendor-specs/bips/bip-0346_ref-impl_txhash_vectors.json: " ++ show (length usable) ++ " of " ++ show (length vecs)
                                      ++ " vectors (" ++ show skipped ++ " rejected by the selector decoder as invalid)")
      , entryAssumptions = [ "the selector is decoded off-chain into flags and two 16-bit selection masks (at most 16 inputs and outputs)"
                           , "the tapscript-context fields (control block hash, spent script hash, OP_CODESEPARATOR position) are witness operands computed from each vector's witness: a Simplicity spend has no tapscript"
                           , "the selector and the expected hash are witness operands" ]
      , entryProgram = \(sel, h) -> Prog (txHashProg sel h)
      , entryVectors = map vec usable ++ neg
      }
    ]
 where
  breakOn pat str | pat `L.isPrefixOf` str = Just (L.drop (length pat) str)
                  | null str = Nothing
                  | otherwise = breakOn pat (tail str)
  strField k str = case breakOn k str of
    Just r -> L.takeWhile (/= '"') (L.drop 1 (L.dropWhile (/= '"') (L.drop 1 (L.dropWhile (/= ':') r))))
    Nothing -> error ("missing " ++ k)
  arrRaw k str = case breakOn k str of
    Just r -> matching (L.dropWhile (/= '[') r)
    Nothing -> error ("missing " ++ k)
  matching = go (0 :: Int)
   where
    go _ [] = []
    go d (c:cs) | c == '[' = c : go (d + 1) cs
                | c == ']' = if d == 1 then [c] else c : go (d - 1) cs
                | otherwise = c : go d cs
  arrField k str = [ L.takeWhile (/= '"') x | x <- map (L.drop 1 . L.dropWhile (/= '"')) (splitC (arrRaw k str)), x /= "" ]
  splitC xs = case break (== ',') xs of
    (a, []) -> [a]
    (a, _:r) -> a : splitC r
  objects str = case L.dropWhile (/= '{') str of
    [] -> []
    (_:r) -> let (o, rest) = break (== '}') r in o : objects rest
  key k o = case L.findIndex (L.isPrefixOf ("\"" ++ k ++ "\"")) (L.tails o) of
    Just i -> L.drop 1 (L.dropWhile (/= ':') (L.drop i o))
    Nothing -> error ("missing key " ++ k)
  field' k o = let v = L.dropWhile (== ' ') (key k o) in if take' 4 v == "null" then "" else L.takeWhile (/= '"') (L.drop 1 (L.dropWhile (/= '"') v))
  take' n = L.take n
  rawField k o = L.takeWhile (`notElem` ",}\n ") (L.dropWhile (== ' ') (key k o))
