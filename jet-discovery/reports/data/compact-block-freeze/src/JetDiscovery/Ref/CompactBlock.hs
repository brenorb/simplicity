-- | Local byte-level reference for the exact bounded BIP152 reconstruction.
-- Raw hash bytes are never explorer/display text and are never reversed here.
module JetDiscovery.Ref.CompactBlock where
import qualified Data.ByteString as B
import Data.Bits
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes(putNoWitnessTx)
import JetDiscovery.Tx
import JetDiscovery.Ref.BitcoinGrowth(sha256d,le64)
import qualified JetDiscovery.Ref.SipHash as Sip

little bytes=sum[toInteger b`shiftL`(8*i)|(i,b)<-zip[0..](B.unpack bytes)]
sha=hashToBytes.sha256
keys header nonce=let seed=sha(header<>le64 nonce)
                  in(fromInteger(little(B.take 8 seed)),fromInteger(little(B.take 8(B.drop 8 seed))))
shortId header nonce rawTransaction=let(k0,k1)=keys header nonce in toInteger(Sip.sipHash24 k0 k1(sha256d rawTransaction)).&.0xffffffffffff
compactSize n=runPut(putCompactSize(fromInteger n))
readCompact raw
 |B.null raw=Nothing
 |tag<253=Just(toInteger tag,B.tail raw)
 |B.length raw<1+size=Nothing
 |value<minimum=Nothing
 |otherwise=Just(value,B.drop(1+size)raw)
 where tag=B.head raw;size=if tag==253 then 2 else if tag==254 then 4 else 8
       minimum=if tag==253 then 253 else if tag==254 then 65536 else 4294967296
       value=little(B.take size(B.tail raw))
requestEncode blockHash indexes
 |B.length blockHash/=32||any(<0)indexes||any(>65535)indexes||or(zipWith(>=)indexes(drop 1 indexes))=error "canonical request indices"
 |otherwise=blockHash<>compactSize(toInteger(length indexes))<>B.concat(map compactSize(zipWith(-)indexes(0:map(+1)indexes)))
requestDecode raw
 |B.length raw<33=Nothing
 |otherwise=do
  (count,after)<-readCompact(B.drop 32 raw)
  if count>65536 then Nothing else do
   (indexes,rest)<-readN count 0 after
   if B.null rest then Just(B.take 32 raw,indexes)else Nothing
 where
  readN 0 _ rest=Just([],rest)
  readN n shift rest=do
   (delta,after)<-readCompact rest
   let index=shift+delta
   if index>65535 then Nothing else do
    (indexes,end)<-readN(n-1)(index+1)after
    Just(index:indexes,end)
canonicalLegacy raw=case parseRawTx raw of
 Right tx->all null(rtWitness tx)&&runPut(putNoWitnessTx(rawToSigTx tx))==raw
 _->False
compactEncode header nonce sid index coinbase
 |B.length header/=80||sid<0||sid>=2^48||index<0||index>=253||not(canonicalLegacy coinbase)=error "bounded compact block"
 |otherwise=header<>le64 nonce<>B.singleton 1<>B.take 6(le64 sid)<>B.singleton 1<>B.singleton(fromInteger index)<>coinbase
compactDecode raw
 |B.length raw<98||B.index raw 88/=1||B.index raw 95/=1||B.index raw 96>=253||not(canonicalLegacy(B.drop 97 raw))=Nothing
 |otherwise=Just(B.take 80 raw,little(B.take 8(B.drop 80 raw)),little(B.take 6(B.drop 89 raw)),toInteger(B.index raw 96),B.drop 97 raw)
responseEncode blockHash transaction
 |B.length blockHash/=32||not(canonicalLegacy transaction)=error "bounded response"
 |otherwise=blockHash<>B.singleton 1<>transaction
responseDecode raw
 |B.length raw<34||B.index raw 32/=1||not(canonicalLegacy(B.drop 33 raw))=Nothing
 |otherwise=Just(B.take 32 raw,B.drop 33 raw)
data Fill=Mempool B.ByteString|Requested B.ByteString Integer B.ByteString B.ByteString deriving(Eq,Show)
fillTransaction(Mempool raw)=raw
fillTransaction(Requested _ _ _ raw)=raw
verify header nonce sid index coinbase fill=B.length header==80&&canonicalLegacy coinbase&&canonicalLegacy transaction
 &&index==0&&sid>=0&&sid<2^48&&shortId header nonce transaction==sid
 &&sha256d coinbase/=sha256d transaction&&sha256d(sha256d coinbase<>sha256d transaction)==B.take 32(B.drop 36 header)&&path
 where
  transaction=fillTransaction fill
  path=case fill of Mempool _->True;Requested requested i response _->requested==sha256d header&&response==sha256d header&&i==1
