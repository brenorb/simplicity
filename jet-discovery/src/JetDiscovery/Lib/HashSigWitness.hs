{-# LANGUAGE GADTs #-}
-- | One fixed-size typed witness for a67-chain/10-node hash signature.
-- Every logical proof field is bound once. The verifier receives only this
-- input value and projects it; it must never reintroduce fields with witness.
module JetDiscovery.Lib.HashSigWitness
 ( HashSigInput, packHashSig, indexT, randomizerT, chainT, authT
 , pair2,pair4,pair8,pair16,pair32,pair64,fieldItems ) where
import Prelude hiding (drop,take)
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Ty.Word

type HashSigInput=((Word32,Word256),((Vector64 Word256,(Word256,(Word256,Word256))),(Vector8 Word256,(Word256,Word256))))

pair2 :: [a] -> (a,a)
pair2 [a,b]=(a,b)
pair2 _=error "HashSigWitness pair2"
pair4 :: [a] -> Vector4 a
pair4 xs=(pair2 (L.take 2 xs),pair2 (L.drop 2 xs))
pair8 :: [a] -> Vector8 a
pair8 xs=(pair4 (L.take 4 xs),pair4 (L.drop 4 xs))
pair16 :: [a] -> Vector16 a
pair16 xs=(pair8 (L.take 8 xs),pair8 (L.drop 8 xs))
pair32 :: [a] -> Vector32 a
pair32 xs=(pair16 (L.take 16 xs),pair16 (L.drop 16 xs))
pair64 :: [a] -> Vector64 a
pair64 xs=(pair32 (L.take 32 xs),pair32 (L.drop 32 xs))

packHashSig :: Word32 -> Word256 -> [Word256] -> [Word256] -> HashSigInput
packHashSig q r ss ap
 | length ss/=67 || length ap/=10=error "HashSigWitness: wrong proof dimensions"
 | otherwise=((q,r),((pair64 (L.take 64 ss),(ss!!64,(ss!!65,ss!!66))),(pair8 (L.take 8 ap),(ap!!8,ap!!9))))

items :: Core term => Vector a b -> [term b a]
items SingleV=[iden]
items (DoubleV v)=map take rec++map drop rec
 where rec=items v

fieldItems :: Core term => Vector a b -> [term b a]
fieldItems=items

indexT :: Core term => term HashSigInput Word32
indexT=take oh
randomizerT :: Core term => term HashSigInput Word256
randomizerT=take ih
chainT :: Core term => Int -> term HashSigInput Word256
chainT i | i>=0 && i<64=drop (take oh) >>> (items vector64!!i)
         | i==64=drop (take ih) >>> oh
         | i==65=drop (take ih) >>> ioh
         | i==66=drop (take ih) >>> iih
         | otherwise=error "HashSigWitness: chain index"
authT :: Core term => Int -> term HashSigInput Word256
authT i | i>=0 && i<8=drop (drop oh) >>> (items vector8!!i)
        | i==8=drop (drop ih) >>> oh
        | i==9=drop (drop ih) >>> ih
        | otherwise=error "HashSigWitness: path index"
