{-# LANGUAGE ScopedTypeVariables, GADTs #-}
-- | Pure direct-block SHRINCS/SLH-DSA n16 WOTS chain, with no witness nodes.
-- The compressed SHA256 seed state is input data. Prefix18 || step4 || node16
-- is38bytes after the seeded64-byte block, so one padded compression suffices.
module JetDiscovery.Lib.ShrincsHash
 ( AddressPrefix,ChainInput,chain,chainRef,seedState ) where
import Prelude hiding (drop,take,and,or,not)
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Arith as Arith
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes (konst,w8)

-- | layer1 || tree8 || type1 || keypair4 || chain4, in big-endian byte order.
-- SHRINCS stateful F uses type16, stateless WOTS F uses type0.
type AddressPrefix=((Word8,Word64),(Word8,(Word32,Word32)))
type ChainInput=(Word256,(AddressPrefix,(Word4,Word128)))

-- | SHA256 compression of pk_seed16 || zero48 under the standard IV.
seedState :: Assert term => term Word128 Word256
seedState=((unit >>> iv) &&& ((iden &&& konst (toWord128 0)) &&& konst (toWord256 0))) >>> hashBlock

chain :: Simplicity term => term ChainInput Word128
chain=unwrap chainWrapped
{-# NOINLINE chainWrapped #-}
chainWrapped :: Jets.WrappedSimplicity ChainInput Word128
chainWrapped=Jets.jetSubst chainRef

-- | For j=start..14, node:=first16(SHA256_compress(state,padded(prefix||j||node))).
-- Padding's encoded total length includes the already compressed64-byte seed
-- block:102bytes=816bits. start=15 returns the supplied node without hashing.
-- The static cost includes15 conditional compressions, regardless of start.
chainRef :: forall term. Assert term => term ChainInput Word128
chainRef=L.foldl' (>>>) iden [step j|j<-[0..14]] >>> iiih
 where
  step j=oh &&& (ioh &&& (iioh &&& ((((iioh >>> nibble8) &&& byte j) >>> Arith.le word8) &&& iden >>> cond (hash j) iiih)))
  nibble8=konst (toWord4 0) &&& iden
  hash j=(oh &&& packBlock (fields j)) >>> hashBlock >>> oh
  fields j=[ioh >>> ooh]++map ((ioh >>> oih) >>>) (byteItems vector8)++[ioh >>> ioh]++
           map ((ioh >>> iioh) >>>) (byteItems vector4)++map ((ioh >>> iiih) >>>) (byteItems vector4)++
           map byte [0,0,0,j]++map (iiih >>>) (byteItems vector16)++
           map byte ([128]++replicate 17 0++[0,0,0,0,0,0,3,48])
  byte :: TyC a => Integer -> term a Word8
  byte=konst.w8

byteItems :: Core term => Word.Vector Word8 b -> [term b Word8]
byteItems SingleV=[iden]
byteItems (DoubleV v)=map take rec++map drop rec
 where rec=byteItems v
packBlock :: (Core term,TyC a) => [term a Word8] -> term a Word512
packBlock xs=p32 (L.take 32 xs) &&& p32 (L.drop 32 xs)
 where
  p32 ys=p16 (L.take 16 ys) &&& p16 (L.drop 16 ys)
  p16 ys=p8 (L.take 8 ys) &&& p8 (L.drop 8 ys)
  p8 ys=p4 (L.take 4 ys) &&& p4 (L.drop 4 ys)
  p4 ys=p2 (L.take 2 ys) &&& p2 (L.drop 2 ys)
  p2 [a,b]=a &&& b
  p2 _=error "SHRINCS direct block width"
