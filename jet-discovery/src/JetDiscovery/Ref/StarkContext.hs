-- | Authenticated reopenings of one checked STARK transcript context.
-- This is a corpus compiler representation, not an additional proof system.
module JetDiscovery.Ref.StarkContext where

import qualified Data.ByteString as B
import Data.Bits (testBit)
import Data.List (foldl')
import qualified JetDiscovery.Ref.FibonacciStark as F
import JetDiscovery.Ref.CircleFri (qm31Bytes)

data Initial = Initial
  { initialTraceRoot :: B.ByteString
  , initialCompositionRoot :: B.ByteString
  , initialZ :: F.Q
  , initialRho :: F.Q
  , initialOod :: [F.Q]
  } deriving (Eq, Show)
data Layer = Layer
  { layerRoot :: B.ByteString
  , layerBeta :: F.Q
  , layerFinal :: F.Q
  } deriving (Eq, Show)
data Certificate a = Certificate { certificateValue :: a, certificatePath :: [B.ByteString] }
  deriving (Eq, Show)
data Certificates = Certificates
  { initialCertificate :: Certificate Initial
  , layerCertificates :: [Certificate Layer]
  } deriving (Eq, Show)

initialBytes v = initialTraceRoot v <> initialCompositionRoot v <>
  qm31Bytes (initialZ v) <> qm31Bytes (initialRho v) <> B.concat (map qm31Bytes (initialOod v))
layerBytes v = layerRoot v <> qm31Bytes (layerBeta v) <> qm31Bytes (layerFinal v)
leaf i payload = F.sha (B.pack [0,fromIntegral i] <> payload)
parent l r = F.sha (B.singleton 1 <> l <> r)

context :: F.Parameters -> F.Proof -> (B.ByteString, Certificates)
context p pr = (head (last levels), Certificates (cert 0 initial) [cert (l+1) v | (l,v) <- zip [0..] layers])
 where
  (_,z,rho,betas,_) = F.challenges p pr
  initial = Initial (F.traceRoot pr) (F.compositionRoot pr) z rho (F.ood pr)
  layers = [Layer r b (F.finalValue pr) | (r,b) <- zip (F.friRoots pr) betas]
  leaves = leaf 0 (initialBytes initial) :
    [if i <= length layers then leaf i (layerBytes (layers!!(i-1))) else leaf i B.empty | i <- [1..15]]
  levels = take 5 (iterate combine leaves)
  combine (l:r:xs) = parent l r : combine xs
  combine [] = []
  combine _ = error "StarkContext: malformed internal Merkle level"
  cert i value = Certificate value [(levels!!depth)!!((i `div` (2^depth)) `xor1` ()) | depth <- [0..3]]
  xor1 x () = if odd x then x-1 else x+1

checkCertificate index payload (Certificate _ path) expected = length path==4 &&
  foldl' (\h (depth,sibling) -> if testBit index depth then parent sibling h else parent h sibling)
    (leaf index payload) (zip [0..] path) == expected

wireEncodable :: F.Parameters -> Certificates -> Bool
wireEncodable p cs = length (layerCertificates cs)==F.traceLog p &&
  validCert initialValues (initialCertificate cs) && all (validCert layerValues) (layerCertificates cs)
 where
  validCert vals (Certificate v path) = length path==4 && all ((==32) . B.length) path && vals v
  wordQ ((a,b),(c,d)) = all (\x -> x>=0 && x<2^(32::Int)) [a,b,c,d]
  initialValues v = B.length (initialTraceRoot v)==32 && B.length (initialCompositionRoot v)==32 &&
    length (initialOod v)==4 && all wordQ (initialZ v:initialRho v:initialOod v)
  layerValues v = B.length (layerRoot v)==32 && all wordQ [layerBeta v,layerFinal v]
