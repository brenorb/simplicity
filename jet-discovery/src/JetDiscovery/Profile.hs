{-# LANGUAGE BangPatterns, GADTs, RankNTypes, ScopedTypeVariables #-}
-- | Static cost profile of a jetted Simplicity DAG.
--
-- For every node of the (shared) DAG we compute
--
-- * its own weight ('niSelf'): the cost the node adds on top of its children,
--   mirroring 'Simplicity.BitMachine.StaticAnalysis.Cost.TermWeight' and
--   @simplicity_analyseBounds@ in C/eval.c,
-- * its inclusive weight ('niTotal'): the static cost bound of the sub-DAG,
-- * its multiplicity ('niMult'): how many times the node is counted in the
--   root's static bound.  Children of @comp@, @pair@, @take@, @drop@, @injl@,
--   @injr@ and @disconnect@ inherit the parent's multiplicity; for @case@ only
--   the more expensive branch does (the bound takes the max).
--
-- Hence @sum [niMult * niSelf]@ equals the root's static bound, and
-- @niMult * niTotal@ is the part of the root's bound spent inside that sub-DAG.
module JetDiscovery.Profile
  ( NodeInfo(..)
  , profile
  , prettyTy
  ) where

import Data.Bits (xor, shiftL, shiftR)
import Data.Foldable (toList)
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Control.Monad.ST (runST)
import Control.Monad (forM_, when)
import Data.Word (Word64)

import qualified Simplicity.Ty as Ty
import Simplicity.Ty (Ty, TyF(..), SomeArrow(..), reifyArrow, unreflect, memoCataTy)
import Simplicity.BitMachine.Ty (bitSize)
import Simplicity.Bitcoin.Inference (TermF(..))

data NodeInfo = NodeInfo
  { niIndex :: !Int
  , niHash  :: !Word64   -- ^ structural hash including constant values and types
  , niShape :: !Word64   -- ^ structural hash ignoring constant word values
  , niKind  :: String    -- ^ combinator name, or @jet:<name>@
  , niSrc   :: Ty
  , niTgt   :: Ty
  , niSelf  :: !Integer  -- ^ milliWU
  , niTotal :: !Integer  -- ^ milliWU, static bound of the sub-DAG
  , niMult  :: !Integer
  , niNodes :: !Int      -- ^ number of distinct DAG nodes in the sub-DAG (upper bound by summing children, capped)
  }

overheadMilli :: Integer
overheadMilli = 100

-- | 64-bit mixing (splitmix64 finaliser).
mix :: Word64 -> Word64
mix z0 = z3
 where
  z1 = (z0 `xor` (z0 `shiftR` 30)) * 0xbf58476d1ce4e5b9
  z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94d049bb133111eb
  z3 = z2 `xor` (z2 `shiftR` 31)

combine :: [Word64] -> Word64
combine = foldl (\acc x -> mix (acc `xor` (x + 0x9e3779b97f4a7c15 + (acc `shiftL` 6) + (acc `shiftR` 2)))) 0x1234567

tyHash :: Ty -> Word64
tyHash = memoCataTy f
 where
  f One = 1
  f (Sum a b) = combine [2, a, b]
  f (Prod a b) = combine [3, a, b]

strHash :: String -> Word64
strHash = combine . map (fromIntegral . fromEnum)

-- | Render a type compactly: words as @W<n>@, @1 + a@ as @S a@.
prettyTy :: Ty -> String
prettyTy t = snd (memoCataTy f t)
 where
  -- (is a word of n bits?, rendering)
  f :: TyF (Maybe Integer, String) -> (Maybe Integer, String)
  f One = (Nothing, "1")
  f (Sum (_, "1") (_, "1")) = (Just 1, "2")
  f (Sum (_, "1") (_, b)) = (Nothing, "S " ++ paren b)
  f (Sum (_, a) (_, b)) = (Nothing, "(" ++ a ++ " + " ++ b ++ ")")
  f (Prod (Just n, _) (Just m, _)) | n == m = (Just (2 * n), "W" ++ show (2 * n))
  f (Prod (_, a) (_, b)) = (Nothing, "(" ++ a ++ ", " ++ b ++ ")")
  paren s | ' ' `elem` s && head s /= '(' = "(" ++ s ++ ")"
          | otherwise = s

-- | Profile a DAG as produced by 'Simplicity.Bitcoin.Dag.jetDag'.
-- @name@ and @cost@ give a jet's display name and its cost in milliWU.
-- @constValue@ returns a hash of a jet's constant payload (for constant-word jets), if any.
profile :: forall f jt w. Foldable f
        => (forall a b. (Ty.TyC a, Ty.TyC b) => jt a b -> String)
        -> (forall a b. (Ty.TyC a, Ty.TyC b) => jt a b -> Integer)
        -> (forall a b. (Ty.TyC a, Ty.TyC b) => jt a b -> Maybe Word64)
        -> f (TermF Ty (SomeArrow jt) w Integer)
        -> [NodeInfo]
profile name cost constValue dag = V.toList infos
 where
  nodes = V.fromList (toList dag)
  len = V.length nodes
  child i off = i - fromInteger off
  base = V.generate len go
  -- (hash, shape, kind, src, tgt, self, total, children, caseChildren, nodes)
  go i = case nodes V.! i of
    Iden a -> leaf "iden" [tyHash a] a a (overheadMilli + bitSize a)
    Unit a -> leaf "unit" [tyHash a] a oneTy overheadMilli
    Injl a b c t -> un "injl" [tyHash a, tyHash b, tyHash c] a (sumTy b c) t
    Injr a b c t -> un "injr" [tyHash a, tyHash b, tyHash c] a (sumTy b c) t
    Take a b c t -> un "take" [tyHash a, tyHash b, tyHash c] (prodTy a b) c t
    Drop a b c t -> un "drop" [tyHash a, tyHash b, tyHash c] (prodTy a b) c t
    Comp a b c s t -> bin "comp" [tyHash a, tyHash b, tyHash c] a c (overheadMilli + bitSize b) s t False
    Case a b c d s t -> bin "case" [tyHash a, tyHash b, tyHash c, tyHash d] (prodTy (sumTy a b) c) d overheadMilli s t True
    Pair a b c s t -> bin "pair" [tyHash a, tyHash b, tyHash c] a (prodTy b c) overheadMilli s t False
    Disconnect a b c d s t -> bin "disconnect" [tyHash a, tyHash b, tyHash c, tyHash d] a (prodTy b d)
                                  (overheadMilli + 2 * bitSize (prodTy w256 a) + bitSize (prodTy b c) + bitSize b) s t False
    Hidden _ -> (strHash "hidden", strHash "hidden", "hidden", oneTy, oneTy, 0, 0, [], False, 1)
    Witness a b _ -> leaf "witness" [tyHash a, tyHash b] a b (overheadMilli + bitSize b)
    Jet (SomeArrow j) ->
      let (ra, rb) = reifyArrow j
          src = unreflect ra
          tgt = unreflect rb
          nm = name j
          h0 = [strHash ("jet:" ++ nm), tyHash src, tyHash tgt]
          hv = maybe h0 (\v -> h0 ++ [v]) (constValue j)
          selfW = overheadMilli + cost j
      in (combine hv, combine h0, "jet:" ++ nm, src, tgt, selfW, selfW, [], False, 1)
   where
    leaf k hs a b w = (combine (strHash k : hs), combine (strHash k : hs), k, a, b, w, w, [], False, 1)
    un k hs a b t = let c = child i t
                        (ch, cs, _, _, _, _, ct, _, _, cn) = base V.! c
                        w = overheadMilli
                    in (combine (strHash k : ch : hs), combine (strHash k : cs : hs), k, a, b, w, w + ct, [c], False, min maxNodes (1 + cn))
    bin k hs a b w s t isCase =
      let cs' = child i s
          ct' = child i t
          (h1, s1, _, _, _, _, t1, _, _, n1) = base V.! cs'
          (h2, s2, _, _, _, _, t2, _, _, n2) = base V.! ct'
          total = if isCase then w + max t1 t2 else w + t1 + t2
      in (combine (strHash k : h1 : h2 : hs), combine (strHash k : s1 : s2 : hs), k, a, b, w, total, [cs', ct'], isCase, min maxNodes (1 + n1 + n2))
  maxNodes = 1000000000
  mults = runST $ do
    m <- MV.replicate len (0 :: Integer)
    when (len > 0) $ MV.write m (len - 1) 1
    forM_ [len - 1, len - 2 .. 0] $ \i -> do
      mi <- MV.read m i
      when (mi /= 0) $ do
        let (_, _, _, _, _, _, _, cs, isCase, _) = base V.! i
        case (isCase, cs) of
          (True, [l, r]) -> do
            let tl = total (base V.! l)
                tr = total (base V.! r)
                pick = if tl >= tr then l else r
            MV.modify m (+ mi) pick
          _ -> forM_ cs $ \c -> MV.modify m (+ mi) c
    V.freeze m
  total (_, _, _, _, _, _, t, _, _, _) = t
  infos = V.imap (\i (h, s, k, a, b, w, t, _, _, nn) -> NodeInfo i h s k a b w t (mults V.! i) nn) base

oneTy :: Ty
oneTy = Ty.one

-- Helpers to build composite types from annotations.
sumTy, prodTy :: Ty -> Ty -> Ty
sumTy = Ty.sum
prodTy = Ty.prod

w256 :: Ty
w256 = iterate (\t -> prodTy t t) (sumTy oneTy oneTy) !! 8
