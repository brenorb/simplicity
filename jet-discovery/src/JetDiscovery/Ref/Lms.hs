-- | Independent ByteString/Integer LMS reference, RFC 8554.
-- LMS_SHA256_M32_H10 with LMOTS_SHA256_N32_W4; deterministic test-only key.
module JetDiscovery.Ref.Lms
 ( Signature(..), identifier, publicRoot, signatureFor, verify, verifyWith, digits, chain ) where

import qualified Data.ByteString as BS
import Data.Bits ((.&.),shiftR,testBit)
import Data.List (foldl')
import JetDiscovery.Tx (sha256,hashToBytes)
import qualified JetDiscovery.Ref.Bip340 as R

type B=BS.ByteString

data Signature=Signature { leafIndex :: Integer, randomizer :: B, chains :: [B], auth :: [B] }
 deriving Show

hash :: B -> B
hash=hashToBytes.sha256

u16,u32 :: Integer -> B
u16=BS.drop 30.R.bytesFromInt
u32=BS.drop 28.R.bytesFromInt

identifier :: B
identifier=BS.take 16 (hash (R.bytesFromInt 0x8554))

chain :: Integer -> Int -> Int -> Int -> B -> B
chain=chainWith identifier

chainWith :: B -> Integer -> Int -> Int -> Int -> B -> B
chainWith ident q i start count x=foldl' (\v j -> hash (ident<>u32 q<>u16 (toInteger i)<>BS.singleton (fromIntegral j)<>v)) x [start..start+count-1]

digits :: B -> [Int]
digits msgHash=ns++[fromIntegral ((cs `shiftR` s).&.15) | s<-[8,4,0]]
 where
  ns=concat [[fromIntegral (b `shiftR` 4),fromIntegral (b .&.15)] | b<-BS.unpack msgHash]
  cs=sum (map (15-) ns) :: Int

secret :: Int -> B
secret i=hash (R.bytesFromInt (0x85540000+toInteger i))

testQ :: Integer
testQ=17

otsPublic :: B
otsPublic=hash (identifier<>u32 testQ<>u16 0x8080<>BS.concat [chain testQ i 0 15 (secret i) | i<-[0..66]])

authPath :: [B]
authPath=[hash (R.bytesFromInt (0xb0000+toInteger i)) | i<-[0..9]]

rootFrom :: B -> Integer -> B -> [B] -> B
rootFrom ident q k siblings=snd (foldl' level (q+1024,hash (ident<>u32 (q+1024)<>u16 0x8282<>k)) siblings)
 where
  level (node,v) sibling=let parent=node `div` 2; (l,r)=if odd node then (sibling,v) else (v,sibling) in
    (parent,hash (ident<>u32 parent<>u16 0x8383<>l<>r))

publicRoot :: B
publicRoot=rootFrom identifier testQ otsPublic authPath

signatureFor :: B -> Signature
signatureFor msg=Signature testQ c ys authPath
 where
  c=hash (R.bytesFromInt 0x8554c)
  ds=digits (hash (identifier<>u32 testQ<>u16 0x8181<>c<>msg))
  ys=[chain testQ i 0 d (secret i) | (i,d)<-zip [0..] ds]

verify :: B -> Signature -> Bool
verify=verifyWith identifier publicRoot

verifyWith :: B -> B -> B -> Signature -> Bool
verifyWith ident expectedRoot msg (Signature q c ys siblings)
 | q<0 || q>=1024 || BS.length ident/=16 || BS.length expectedRoot/=32 || BS.length c/=32 || length ys/=67 || length siblings/=10=False
 | any ((/=32).BS.length) (ys++siblings)=False
 | otherwise=rootFrom ident q pk siblings==expectedRoot
 where
  ds=digits (hash (ident<>u32 q<>u16 0x8181<>c<>msg))
  pk=hash (ident<>u32 q<>u16 0x8080<>BS.concat [chainWith ident q i d (15-d) y | (i,(d,y))<-zip [0..] (zip ds ys)])
