-- | A small, complete circle-FRI low-degree test over M31 (as in StarkWare's
-- Stwo, with SHA-256 Merkle commitments as in its Bitcoin verifier), used to
-- produce real proofs for "JetDiscovery.Corpus.StarkFri".
--
-- * Domain: x-coordinates of the circle coset Q0 + <G0> of size 2^n, where G0
--   has order 2^n and Q0 order 2^(n+2) (so x-coordinates are distinct).  Points
--   j and j + N/2 are antipodal (x and -x); the doubling map x -> 2x^2 - 1 takes
--   layer l to layer l + 1.
-- * Values in QM31.  Layer l is committed by a Merkle tree whose leaves are
--   SHA-256 of each 16-byte value, with antipodal pairs as siblings.
-- * Fold: f'(pi(x)) = (f(x) + f(-x)) + alpha * (f(x) - f(-x)) / x.
-- * Fiat-Shamir: h0 = sha256(root0); h_l = sha256(h_{l-1} || root_l); alpha_l from h_l;
--   after the last fold the prover sends the constant c and the queries are
--   bytes of sha256(h_{L-1} || c), masked to pair indices.
module JetDiscovery.Ref.CircleFri
  ( logN, folds, queries
  , gen, circleMul, circlePow, q0, g0
  , Proof(..), QueryProof(..), prove, verifyRef
  , qm31Bytes, alphaOf
  ) where

import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, testBit, (.&.))

import JetDiscovery.Corpus.Stark (p31, hMul, hFold, HQ)
import JetDiscovery.Tx (sha256, hashToBytes)

logN, folds, queries :: Int
logN = 8
folds = 6
queries = 3

type Pt = (Integer, Integer)

gen :: Pt
gen = (2, 1268011823)

circleMul :: Pt -> Pt -> Pt
circleMul (a, b) (c, d) = ((a * c - b * d) `mod` p31, (a * d + b * c) `mod` p31)

circlePow :: Pt -> Integer -> Pt
circlePow _ 0 = (1, 0)
circlePow x e | even e = let h = circlePow x (e `div` 2) in circleMul h h
              | otherwise = circleMul x (circlePow x (e - 1))

g0, q0 :: Pt
g0 = circlePow gen (2 ^ (31 - logN))
q0 = circlePow gen (2 ^ (31 - logN - 2))

point :: Int -> Int -> Pt
point l j = circleMul (circlePow q0 (2 ^ l)) (circlePow g0 (2 ^ l * toInteger j))

powMod :: Integer -> Integer -> Integer
powMod _ 0 = 1
powMod b e | even e = let h = powMod b (e `div` 2) in h * h `mod` p31
           | otherwise = b * powMod b (e - 1) `mod` p31

inv :: Integer -> Integer
inv a = powMod a (p31 - 2)

qm31Bytes :: HQ -> BS.ByteString
qm31Bytes ((a, b), (c, d)) = BS.concat [ BS.pack [ fromIntegral (w `shiftR` (8 * i)) | i <- [3, 2, 1, 0] ] | w <- [a, b, c, d] ]

sha :: BS.ByteString -> BS.ByteString
sha = hashToBytes . sha256

-- | QM31 from a 32-byte hash: the first four big-endian words masked to 31 bits (p reduces to 0).
alphaOf :: BS.ByteString -> HQ
alphaOf h = let w i = (BS.foldl' (\a x -> a * 256 + toInteger x) 0 (BS.take 4 (BS.drop (4 * i) h)) .&. (2 ^ (31 :: Int) - 1)) `mod` p31
            in ((w 0, w 1), (w 2, w 3))

-- | Merkle tree over pair leaves; returns all levels from the pair nodes up to the root.
merkle :: [HQ] -> [[BS.ByteString]]
merkle vs = takeWhile (not . null) (iterate up pairsLevel)
 where
  half = length vs `div` 2
  pairsLevel = [ sha (sha (qm31Bytes (vs !! j)) <> sha (qm31Bytes (vs !! (j + half)))) | j <- [0 .. half - 1] ]
  up [_] = []
  up xs = [ sha (a <> b) | (a, b) <- pairs xs ]
  pairs (a:b:r) = (a, b) : pairs r
  pairs _ = []

data QueryProof = QueryProof
  { qpPairs :: [(HQ, HQ)]              -- ^ per layer: (f(x), f(-x))
  , qpPaths :: [[BS.ByteString]]       -- ^ per layer: siblings from the pair node up
  , qpXinv :: [Integer]                -- ^ per layer: 1 / x
  }

data Proof = Proof { prRoots :: [BS.ByteString], prConst :: HQ, prQueries :: [(Int, QueryProof)] }

-- | Prove that the evaluations of @coeffs@ (a polynomial in x, degree < 2^(logN - 2)) on the domain are low degree.
-- 'cheat' replaces the layer-0 evaluations by arbitrary values (a non-low-degree "proof").
prove :: Bool -> [HQ] -> Proof
prove cheat coeffs = Proof roots c qs
 where
  n0 = 2 ^ logN :: Int
  evalAt x = foldr (\a acc -> qAdd a (qScale acc x)) ((0, 0), (0, 0)) coeffs
  layer0 = [ if cheat then ((toInteger j * 7919 + 13) `mod` p31, (3, 4)) `withPad` () else evalAt (fst (point 0 j)) | j <- [0 .. n0 - 1] ]
  withPad (a, (b, c')) () = ((a, b), (c', 1))
  layers = take (folds + 1) (iterate' 0 layer0)
  iterate' l vs = vs : if l == folds then [] else iterate' (l + 1) (foldLayer l vs)
  foldLayer l vs = let half = length vs `div` 2 in
    [ hFold (vs !! j) (vs !! (j + half)) (inv (fst (point l j))) (alphas !! l) | j <- [0 .. half - 1] ]
  trees = map merkle (take folds layers)
  roots = map (head . last) trees
  hs = scanl1 (\h r -> sha (h <> r)) (sha (head roots) : tail roots)
  hChain = sha (head roots) : zipWith (\h r -> sha (h <> r)) hChain (tail roots)
  alphas = map alphaOf hChain
  c = head (layers !! folds)
  seed = sha (last hChain <> qm31Bytes c)
  qIdx = [ fromIntegral (BS.index seed k) .&. (2 ^ (logN - 1) - 1) | k <- [0 .. queries - 1] ]
  qs = [ (q, QueryProof [ let vs = layers !! l; half = length vs `div` 2; j = q `mod` half in (vs !! j, vs !! (j + half)) | l <- [0 .. folds - 1] ]
                        [ let tr = trees !! l; j = q `mod` (2 ^ (logN - 1 - l)) in [ (tr !! m) !! ((j `shiftR` m) `xorBit` ()) | m <- [0 .. length tr - 2] ] | l <- [0 .. folds - 1] ]
                        [ inv (fst (point l (q `mod` (2 ^ (logN - 1 - l))))) | l <- [0 .. folds - 1] ])
       | q <- qIdx ]
  xorBit k () = if testBit k 0 then k - 1 else k + 1

qAdd :: HQ -> HQ -> HQ
qAdd ((a, b), (c, d)) ((e, f), (g, h)) = (((a + e) `mod` p31, (b + f) `mod` p31), ((c + g) `mod` p31, (d + h) `mod` p31))

qScale :: HQ -> Integer -> HQ
qScale ((a, b), (c, d)) s = ((hMul a s, hMul b s), (hMul c s, hMul d s))

-- | Reference verifier (same checks as the Simplicity program).
verifyRef :: Proof -> Bool
verifyRef (Proof roots c qs) = and [ checkQuery q qp | (q, qp) <- qs ] && map fst qs == qIdx
 where
  hChain = sha (head roots) : zipWith (\h r -> sha (h <> r)) hChain (tail roots)
  alphas = map alphaOf hChain
  seed = sha (last hChain <> qm31Bytes c)
  qIdx = [ fromIntegral (BS.index seed k) .&. (2 ^ (logN - 1) - 1) | k <- [0 .. queries - 1] ]
  checkQuery q (QueryProof prs paths xinvs) = go 0 (fst (point 0 q))
   where
    go l x
      | l == folds = True
      | otherwise =
          let (a, b) = prs !! l
              j = q `mod` (2 ^ (logN - 1 - l))
              node0 = sha (sha (qm31Bytes a) <> sha (qm31Bytes b))
              root = foldl (\nd (m, s) -> if testBit j m then sha (s <> nd) else sha (nd <> s)) node0 (zip [0 ..] (paths !! l))
              xinv = xinvs !! l
              g = hFold a b xinv (alphas !! l)
              nextOk | l == folds - 1 = g == c
                     | otherwise = let (na, nb) = prs !! (l + 1) in if testBit q (logN - l - 2) then g == nb else g == na
              px = (2 * x * x - 1) `mod` p31
              x' = if l < folds - 1 && testBit q (logN - l - 2) then (p31 - px) `mod` p31 else px
          in root == roots !! l && x * xinv `mod` p31 == 1 && nextOk && go (l + 1) x'
