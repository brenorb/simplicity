-- | Small independent Keccak-256 reference for derived contract vectors.
-- Keccak padding (0x01), not FIPS SHA3 padding (0x06).
module JetDiscovery.Ref.Keccak (keccak256) where
import qualified Data.ByteString as B
import Data.Bits
import Data.Word
import Data.List (foldl')

rc :: [Word64]
rc = [0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000080008081,0x8000000000008080,0x80000001,0x8000000080008008]
rot :: [Int]
rot = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]
perm :: [Word64] -> [Word64]
perm = flip (foldl' rnd) rc
 where
 rnd a r = [ (b!!i `xor` (complement (b!!((x+1)`mod`5+5*y)) .&. b!!((x+2)`mod`5+5*y))) `xor` (if i==0 then r else 0) | i<-[0..24], let (y,x)=i`divMod`5 ]
  where
   c = [foldl1 xor [a!!(x+5*y)|y<-[0..4]]|x<-[0..4]]
   t = [a!!i `xor` c!!((x+4)`mod`5) `xor` rotateL (c!!((x+1)`mod`5)) 1|i<-[0..24],let x=i`mod`5]
   b = [head [rotateL (t!!(x+5*y)) (rot!!(x+5*y))|x<-[0..4],y<-[0..4], y==u, (2*x+3*y)`mod`5==v] | v<-[0..4],u<-[0..4]]
keccak256 :: B.ByteString -> B.ByteString
keccak256 msg = B.pack [fromIntegral ((st!!(i`div`8)) `shiftR` (8*(i`mod`8))) | i<-[0..31]]
 where
  n = 136 - B.length msg `mod` 136
  pad | n==1 = B.singleton 0x81
      | otherwise = B.pack (1:replicate (n-2) 0 ++ [0x80])
  chunks b | B.null b = [] | otherwise = B.take 136 b : chunks (B.drop 136 b)
  lane b = B.foldr (\x a -> fromIntegral x + shiftL a 8) 0 b
  st = foldl' (\a b -> perm [a!!i `xor` (if i<17 then lane (B.take 8 (B.drop (8*i) b)) else 0)|i<-[0..24]]) (replicate 25 0) (chunks (msg<>pad))
