{-# LANGUAGE ScopedTypeVariables #-}
-- | A complete circle-FRI low-degree test verifier over M31 with SHA-256
-- Merkle commitments and Fiat-Shamir, verifying real proofs from
-- "JetDiscovery.Ref.CircleFri" (domain 2^8, blowup 4, 6 folds to a constant,
-- 3 queries).  FRI is the bulk of a STARK verifier; the rest (trace and
-- composition openings, DEEP quotients) adds Merkle openings and a few
-- extension-field evaluations per query.
module JetDiscovery.Corpus.StarkFri
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import Data.Bits (testBit)
import qualified Data.List as L

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Word as Word
import Simplicity.Programs.Sha256.Lib
import Simplicity.Ty.Word

import JetDiscovery.Corpus.Stark (m31Mul, m31Add, m31Sub, m31Fix, friFold, toQ, QM31, M31)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.Kernels (sha256Pair)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.CircleFri as Ref

pick :: (Core term, TyC x, TyC c) => Bool -> term x c -> term (x, x) c
pick True = drop
pick False = take

bit8 :: Core term => Int -> term Word8 Bit
bit8 k = pick (testBit p 2) (pick (testBit p 1) (pick (testBit p 0) iden)) where p = 7 - k

byteAt :: Core term => Int -> term Word256 Word8
byteAt k = pick (testBit k 4) (pick (testBit k 3) (pick (testBit k 2) (pick (testBit k 1) (pick (testBit k 0) iden))))

type T6 a = (a, (a, (a, (a, (a, a)))))
type E = (T6 QM31, (Word8, (Word8, Word8)))   -- (alphas, query pair indices)

at6 :: (Core term, TyC a, TyC c) => Int -> term a c -> term (T6 a) c
at6 0 t = take t
at6 1 t = drop (take t)
at6 2 t = drop (drop (take t))
at6 3 t = drop (drop (drop (take t)))
at6 4 t = drop (drop (drop (drop (take t))))
at6 _ t = drop (drop (drop (drop (drop t))))

qAt :: Core term => Int -> term (Word8, (Word8, Word8)) Word8
qAt 0 = oh
qAt 1 = ioh
qAt _ = iih

sha16 :: Assert term => term Word128 Word256
sha16 = (unit >>> ctx8Init) &&& iden >>> ctx8Add16 >>> ctx8Finalize

sha32 :: Assert term => term Word256 Word256
sha32 = (unit >>> ctx8Init) &&& iden >>> ctx8Add32 >>> ctx8Finalize

-- | QM31 from a hash: the first four words masked to 31 bits, p reduced to 0.
alphaFrom :: Assert term => term Word256 QM31
alphaFrom = oh >>> ((oh >>> (w2)) &&& (ih >>> w2))
 where
  w = (iden &&& konst (w32 0x7fffffff)) >>> Word.bitwise_and word32 >>> m31Fix
  w2 = (oh >>> w) &&& (ih >>> w)

circleMul :: Assert term => term ((M31, M31), (M31, M31)) (M31, M31)
circleMul = (((ooh &&& ioh >>> m31Mul) &&& (oih &&& iih >>> m31Mul)) >>> m31Sub)
        &&& (((ooh &&& iih >>> m31Mul) &&& (oih &&& ioh >>> m31Mul)) >>> m31Add)

ordered :: (Core term, TyC s) => term s Bit -> term s Word256 -> term s Word256 -> term s Word512
ordered b node sib = (b &&& (node &&& sib)) >>> cond (ih &&& oh) iden

data QW = QW { qwPairs :: [(QM31, QM31)], qwPaths :: [[Word256]], qwXinv :: [M31] }
data FW = FW { fwRoots :: [Word256], fwConst :: QM31, fwQueries :: [QW] }

friVerify :: forall term. (Assert term, Witness term) => FW -> term () ()
friVerify fw = env >>> L.foldl' (\acc (k, qw) -> (acc &&& query k qw) >>> unit) unit (zip [0 ..] (fwQueries fw))
 where
  n = Ref.logN
  nf = Ref.folds
  rootT :: forall a. TyC a => Int -> term a Word256
  rootT l = witness (fwRoots fw !! l)
  cT :: forall a. TyC a => term a QM31
  cT = witness (fwConst fw)
  -- (h0, ..., h5): h0 = sha256(root0), h_l = sha256(h_{l-1} || root_l)
  nxt l = (iden &&& rootT l) >>> sha256Pair
  chain :: term Word256 (T6 Word256)
  chain = iden &&& (nxt 1 >>> (iden &&& (nxt 2 >>> (iden &&& (nxt 3 >>> (iden &&& (nxt 4 >>> (iden &&& nxt 5))))))))
  alphas :: term (T6 Word256) (T6 QM31)
  alphas = at6 0 alphaFrom &&& (at6 1 alphaFrom &&& (at6 2 alphaFrom &&& (at6 3 alphaFrom &&& (at6 4 alphaFrom &&& at6 5 alphaFrom))))
  -- queries: bytes of sha256(h5 || c), masked to pair indices
  seed :: term (T6 Word256) Word256
  seed = (((unit >>> ctx8Init) &&& at6 5 iden >>> ctx8Add32) &&& cT >>> ctx8Add16) >>> ctx8Finalize
  qb k = (byteAt k &&& konst (w8 (2 ^ (n - 1) - 1))) >>> Word.bitwise_and word8
  env :: term () E
  env = (rootT 0 >>> sha32 >>> chain) >>> (alphas &&& (seed >>> (qb 0 &&& (qb 1 &&& qb 2))))
  query :: Int -> QW -> term E ()
  query k qw = (iden &&& x0) >>> L.foldl' (\acc l -> acc >>> layer l) iden [0 .. nf - 1] >>> unit
   where
    qbit :: Int -> term (E, M31) Bit
    qbit b = take (drop (qAt k >>> bit8 b))
    -- x0 = x(Q0 + q G0): multiply in G0^(2^b) for each set bit b of the query index
    x0 :: term E M31
    x0 = (iden &&& konst (pt Ref.q0)) >>> L.foldl' (\acc b -> acc >>> stepPt b) iden [0 .. n - 2] >>> drop oh
    stepPt b = oh &&& ((take (drop (qAt k >>> bit8 b)) &&& ih) >>> cond ((iden &&& konst (pt (Ref.circlePow Ref.g0 (2 ^ b)))) >>> circleMul) iden)
    pt (x, y) = (w32 x, w32 y)
    layer :: Int -> term (E, M31) (E, M31)
    layer l = (((merkleOk &&& xinvOk) &&& nextOk) &&& (oh &&& x')) >>> ih
     where
      (pa, pb) = qwPairs qw !! l
      sibs = qwPaths qw !! l
      xi = qwXinv qw !! l
      node0 = ((witness pa >>> sha16) &&& (witness pb >>> sha16)) >>> sha256Pair
      node = L.foldl' (\nd (m, s) -> ordered (qbit m) nd (witness s) >>> sha256Pair) node0 (zip [0 ..] sibs)
      merkleOk = (node &&& rootT l) >>> eq >>> verify
      xinvOk = (((ih &&& witness xi) >>> m31Mul) &&& konst (w32 1)) >>> eq >>> verify
      g = ((witness pa &&& witness pb) &&& (witness xi &&& take (take (at6 l iden)))) >>> friFold
      nextOk | l == nf - 1 = (g &&& cT) >>> eq >>> verify
             | otherwise = let (na, nb) = qwPairs qw !! (l + 1)
                           in (g &&& ((qbit (n - l - 2) &&& unit) >>> cond (witness nb) (witness na))) >>> eq >>> verify
      px = ih >>> (iden &&& iden >>> m31Mul) >>> ((iden &&& iden >>> m31Add) &&& konst (w32 1)) >>> m31Sub
      x' | l == nf - 1 = px
         | otherwise = (qbit (n - l - 2) &&& px) >>> cond ((konst (w32 0) &&& iden) >>> m31Sub) iden

entries :: [Entry]
entries =
  [ Entry
    { entryId = "stark-fri-verifier"
    , entryTitle = "Complete circle-FRI verifier: Merkle openings, folds and Fiat-Shamir (2^8 domain, 6 folds, 3 queries)"
    , entrySpec = "Circle FRI over M31 (Haboeck, Levit, Papini, ePrint 2024/278), SHA-256 commitments as in StarkWare's Bitcoin verifier"
    , entryCategory = Stark
    , entryVectorSource = Derived "proofs from JetDiscovery.Ref.CircleFri; expected outcomes match its reference verifier"
    , entryAssumptions = [ "domain 2^8, blowup 4, 6 folds to a constant, 3 queries: toy security, real protocol"
                         , "the proof is witness data; the committed roots are witness operands" ]
    , entryProgram = \fw -> Prog (friVerify fw)
    , entryVectors =
        [ Vector ("honest proof" ++ note honest) env (toFW honest) Accept
        , Vector ("evaluations not of low degree (reference " ++ (if Ref.verifyRef cheat then "accepts: unlucky queries" else "rejects") ++ ")") env (toFW cheat) (if Ref.verifyRef cheat then Accept else Reject)
        , Vector "tampered layer-2 value" env (toFW (tamper honest)) Reject
        , Vector "wrong final constant" env ((toFW honest) { fwConst = toQ ((1, 2), (3, 4)) }) Reject ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  coeffs = [ ((toInteger i * 31337 + 1) `mod` (2 ^ (31 :: Int) - 1), (toInteger i * 7, 5), (0, toInteger i)) `asQ` () | i <- [0 .. 63 :: Int] ]
  asQ (a, (b, c), (d, e)) () = ((a, b), (c + d, e))
  honest = Ref.prove False coeffs
  cheat = Ref.prove True coeffs
  note p = if Ref.verifyRef p then "" else " (REFERENCE REJECTS)"
  tamper (Ref.Proof r c qs) = Ref.Proof r c (case qs of
    ((q, Ref.QueryProof prs ps xs):rest) -> (q, Ref.QueryProof (L.take 2 prs ++ [ (((0, 0), (0, 9)), snd (prs !! 2)) ] ++ L.drop 3 prs) ps xs) : rest
    [] -> [])
  toFW (Ref.Proof r c qs) = FW (map w256FromBytes r) (toQ c)
    [ QW [ (toQ a, toQ b) | (a, b) <- prs ] [ map w256FromBytes p | p <- ps ] (map w32 xs) | (_, Ref.QueryProof prs ps xs) <- qs ]
