-- | Complete degree256 ML-DSA transform family. The reference evaluates the
-- polynomial directly at FIPS204 equation2.1 roots, not by butterflies.
module JetDiscovery.Ref.MlDsaNtt
 (q,zeta,powMod,bitRev8,zetas,forward,inverse,forwardButterfly,inverseButterfly,cases,selfCheck) where
import qualified Data.List as L
import Data.Bits(testBit)
q,zeta :: Integer
q=8380417
zeta=1753
powMod :: Integer -> Integer -> Integer
powMod _ 0=1
powMod a e | even e=let h=powMod a(e`div`2)in h*h`mod`q
           | otherwise=a*powMod a(e-1)`mod`q
bitRev8 :: Int -> Integer
bitRev8 i=sum[2^(7-j)|j<-[0..7],testBit i j]
zetas :: [Integer]
zetas=[powMod zeta(bitRev8 i)|i<-[0..255]]
valid xs=length xs==256&&all(\x->x>=0&&x<q)xs
roots=[powMod zeta(2*bitRev8 i+1)|i<-[0..255]]
forward :: [Integer] -> Maybe [Integer]
forward xs | not(valid xs)=Nothing
           | otherwise=Just[L.foldr(\c a->(c+r*a)`mod`q)0 xs|r<-roots]
inverse :: [Integer] -> Maybe [Integer]
inverse xs | not(valid xs)=Nothing
           | otherwise=Just[(8347681*sum[yi*powMod r((q-1-j)`mod`(q-1))`mod`q|(yi,r)<-zip xs roots])`mod`q|j<-[0..255]]
replace i value xs=take i xs++[value]++drop(i+1)xs
forwardButterfly xs=L.foldl' stage xs[0..7]
 where
  stage a d=L.foldl' block a[0..2^d-1]
   where
    len=128`div`2^d
    block b i=L.foldl' pair b[2*len*i..2*len*i+len-1]
     where z=zetas!!(2^d+i)
           pair b j=let u=b!!j;t=z*(b!!(j+len))`mod`q
                     in replace(j+len)((u-t)`mod`q)(replace j((u+t)`mod`q)b)
inverseButterfly xs=map(\x->8347681*x`mod`q)(L.foldl' stage xs[7,6..0])
 where
  stage a d=L.foldl' block a[0..2^d-1]
   where
    len=128`div`2^d
    block b i=L.foldl' pair b[2*len*i..2*len*i+len-1]
     where z=negate(zetas!!(2^(d+1)-1-i))
           pair b j=let u=b!!j;v=b!!(j+len)
                     in replace(j+len)(z*(u-v)`mod`q)(replace j((u+v)`mod`q)b)
cases :: [[Integer]]
cases=[replicate 256 0,1:replicate 255 0,0:1:replicate 254 0,[0..255],replicate 256(q-1),[(i^7+17*i+123)`mod`q|i<-[0..255]]]
selfCheck :: Bool
selfCheck=all check cases&&forward(q:replicate 255 0)==Nothing&&inverse(replicate 255 0)==Nothing
 where check x=case forward x of
        Nothing->False
        Just y->forwardButterfly x==y&&inverseButterfly y==x&&inverse y==Just x
