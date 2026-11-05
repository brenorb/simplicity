-- | Independent byte/Word64 SHAKE256-2000 reference, FIPS202. The fixed250-byte
-- output crosses the136-byte rate and matches six complete NIST CAVP cases.
module JetDiscovery.Ref.Shake256(shake250,permute) where
import qualified Data.ByteString as BS
import Data.Word(Word64)
import Data.Bits
import qualified Data.List as L
at table key=case lookup key table of Just x->x;_->error "incomplete Keccak coordinate table"
roundConstants :: [Word64]
roundConstants=[0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000080008081,0x8000000000008080,0x80000001,0x8000000080008008]
offset x y=[[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]]!!x!!y
permute :: [Word64] -> [Word64]
permute input
 | length input/=25=error "SHAKE Keccak state requires25lanes"
 | otherwise=L.foldl' one input roundConstants
 where
  one xs constant=[at chi(x,y)`xor`(if x==0&&y==0 then constant else 0)|y<-[0..4],x<-[0..4]]
   where
    a=[((x,y),xs!!(x+5*y))|x<-[0..4],y<-[0..4]]
    parity x=L.foldl1' xor[at a(x,y)|y<-[0..4]]
    theta=[((x,y),at a(x,y)`xor`parity((x+4)`mod`5)`xor`rotateL(parity((x+1)`mod`5))1)|x<-[0..4],y<-[0..4]]
    rhoPi=[((y,(2*x+3*y)`mod`5),rotateL(at theta(x,y))(offset x y))|x<-[0..4],y<-[0..4]]
    chi=[((x,y),at rhoPi(x,y)`xor`(complement(at rhoPi((x+1)`mod`5,y)).&.at rhoPi((x+2)`mod`5,y)))|x<-[0..4],y<-[0..4]]
shake250 :: BS.ByteString -> Maybe BS.ByteString
shake250 msg
 | BS.length msg>511=Nothing
 | otherwise=Just(BS.take 136(bytes state)<>BS.take 114(bytes(permute state)))
 where
  remaining=136-BS.length msg`mod`136
  padding=if remaining==1 then BS.singleton 0x9f else BS.pack(0x1f:replicate(remaining-2)0++[0x80])
  chunks b | BS.null b=[]
           | otherwise=BS.take 136 b:chunks(BS.drop 136 b)
  lane b=BS.foldr(\x a->fromIntegral x+(a`shiftL`8))0 b
  absorb a b=permute[a!!i`xor`(if i<17 then lane(BS.take 8(BS.drop(8*i)b))else 0)|i<-[0..24]]
  state=L.foldl' absorb(replicate 25 0)(chunks(msg<>padding))
  bytes s=BS.pack[fromIntegral((s!!(i`div`8))`shiftR`(8*(i`mod`8)))|i<-[0..135]]
