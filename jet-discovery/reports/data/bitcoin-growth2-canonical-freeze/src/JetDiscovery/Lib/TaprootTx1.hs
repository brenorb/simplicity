{-# LANGUAGE ScopedTypeVariables #-}
-- | Exact bounded Bitcoin one-input transaction encoding/BIP341 DEFAULT.
-- All inputs are P2TR with empty scriptSig/no annex. Outputs are one or two
-- P2TR outputs, optionally followed by the actual zero-value P2A fee anchor.
-- This is a reusable component; no application/count credit by itself.
module JetDiscovery.Lib.TaprootTx1
 (Input,Out,TxData,txid,defaultMessage,outputHash,appendConst,append,constant
 ,previous,index,value,key,sequence,version,locktime) where
import Prelude hiding(drop,take,sequence)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer(ctxWith)
import qualified JetDiscovery.Ref.Bip340 as R

-- Previous txid is the raw32-byte digest in actual wire order.
type Input=((Word256,Word32),(Word64,(Word256,(Word32,(Word32,Word32)))))
type Out=(Word64,Word256)
type TxData=(Input,(Out,Out))
previous :: Core t => t Input Word256
previous=ooh
index :: Core t => t Input Word32
index=oih
value :: Core t => t Input Word64
value=ioh
key :: Core t => t Input Word256
key=iioh
sequence :: Core t => t Input Word32
sequence=ih>>>ih>>>ih>>>oh
version :: Core t => t Input Word32
version=ih>>>ih>>>ih>>>ih>>>oh
locktime :: Core t => t Input Word32
locktime=ih>>>ih>>>ih>>>ih>>>ih
appendConst :: Assert t => B.ByteString -> t Ctx8 Ctx8
appendConst bytes|B.null bytes=iden
 |otherwise=piece n(B.take n bytes)>>>appendConst(B.drop n bytes)
 where
  n=P.head[k|k<-[32,16,8,4,2,1],k<=B.length bytes]
  piece 32 b=ctxWith(konst(w256FromBytes b))ctx8Add32
  piece 16 b=ctxWith(konst(toWord128(R.intFromBytes b)))ctx8Add16
  piece 8 b=ctxWith(konst(w64(R.intFromBytes b)))ctx8Add8
  piece 4 b=ctxWith(konst(w32(R.intFromBytes b)))ctx8Add4
  piece 2 b=ctxWith(konst(w16(R.intFromBytes b)))ctx8Add2
  piece _ b=ctxWith(konst(w8(R.intFromBytes b)))ctx8Add1
append :: (Assert t,TyC a,TyC b) => t a b -> t(Ctx8,b)Ctx8 -> t(a,Ctx8)(a,Ctx8)
append f jet=oh&&&((ih&&&(oh>>>f))>>>jet)
constant :: (Assert t,TyC a) => B.ByteString -> t(a,Ctx8)(a,Ctx8)
constant b=oh&&&(ih>>>appendConst b)
start :: (Assert t,TyC a) => t a(a,Ctx8)
start=iden&&&(unit>>>ctx8Init)
out :: Core t => Int -> t TxData Out
out 0=ioh
out 1=iih
out _=error "TaprootTx1 output index"
outputs :: Assert t => Int -> Bool -> t(TxData,Ctx8)(TxData,Ctx8)
outputs n anchor
 |n<1||n>2=error "TaprootTx1 output bound"
 |otherwise=L.foldr(>>>)iden[append(out i>>>oh)ctxAddLE64>>>constant(B.pack[0x22,0x51,0x20])>>>append(out i>>>ih)ctx8Add32|i<-[0..n-1]]
   >>>if anchor then constant(B.replicate 8 0<>B.pack[4,0x51,2,0x4e,0x73])else iden
outputHash :: Assert t => Int -> Bool -> t TxData Word256
outputHash n anchor=start>>>outputs n anchor>>>ih>>>ctx8Finalize
doubleHash :: Assert t => t Word256 Word256
doubleHash=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
txid :: Assert t => Int -> Bool -> t TxData Word256
txid n anchor=start>>>append(oh>>>version)ctxAddLE32>>>constant(B.singleton 1)
 >>>append(oh>>>previous)ctx8Add32>>>append(oh>>>index)ctxAddLE32>>>constant(B.singleton 0)
 >>>append(oh>>>sequence)ctxAddLE32>>>constant(B.singleton(fromIntegral(n+if anchor then 1 else 0)))
 >>>outputs n anchor>>>append(oh>>>locktime)ctxAddLE32>>>ih>>>ctx8Finalize>>>doubleHash
prevoutsHash :: Assert t => t TxData Word256
prevoutsHash=start>>>append(oh>>>previous)ctx8Add32>>>append(oh>>>index)ctxAddLE32>>>ih>>>ctx8Finalize
amountsHash :: Assert t => t TxData Word256
amountsHash=start>>>append(oh>>>value)ctxAddLE64>>>ih>>>ctx8Finalize
scriptsHash :: Assert t => t TxData Word256
scriptsHash=start>>>constant(B.pack[0x22,0x51,0x20])>>>append(oh>>>key)ctx8Add32>>>ih>>>ctx8Finalize
sequencesHash :: Assert t => t TxData Word256
sequencesHash=start>>>append(oh>>>sequence)ctxAddLE32>>>ih>>>ctx8Finalize
-- Leaf hash is ignored in keypath mode; scriptpath always has key_version0
-- and no executed OP_CODESEPARATOR. There is exactly one actual input/index0.
defaultMessage :: Assert t => Int -> Bool -> Bool -> t(TxData,Word256)Word256
defaultMessage n anchor scriptPath=(iden&&&(unit>>>ctx8InitTag "TapSighash"))
 >>>constant(B.pack[0,0])>>>append(oh>>>oh>>>version)ctxAddLE32>>>append(oh>>>oh>>>locktime)ctxAddLE32
 >>>append(oh>>>prevoutsHash)ctx8Add32>>>append(oh>>>amountsHash)ctx8Add32
 >>>append(oh>>>scriptsHash)ctx8Add32>>>append(oh>>>sequencesHash)ctx8Add32
 >>>append(oh>>>outputHash n anchor)ctx8Add32
 >>>constant(B.pack[if scriptPath then 2 else 0,0,0,0,0])
 >>>(if scriptPath then append ih ctx8Add32>>>constant(B.pack[0,255,255,255,255])else iden)
 >>>ih>>>ctx8Finalize
