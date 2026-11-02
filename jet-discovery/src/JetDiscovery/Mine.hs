-- | Phase 2: mine the jet-substituted DAGs of the whole corpus for repeated,
-- expensive sub-DAGs.
--
-- Each node of each program's profile ("JetDiscovery.Profile") contributes
-- @mult * total@ milliWU to its program's static bound.  Nodes are grouped
-- across programs by structural hash ('niHash': exact, including constant
-- values) or by shape ('niShape': constant word values ignored, so for
-- example SHRINCS's F calls for different chain and hash indices coincide).
--
-- Only repeated nodes (multiplicity >= 2 in some program, or present in >= 2
-- programs) that are not already a single jet are reported: a node with
-- multiplicity 1 in one program is just a piece of that program's root.
module JetDiscovery.Mine
  ( Group(..)
  , mine
  , groupsMarkdown
  , groupsTsv
  ) where

import Data.List (sortBy, intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Ord (comparing, Down(..))
import Data.Word (Word64)
import Numeric (showHex, showFFloat)

import JetDiscovery.Profile (NodeInfo(..), prettyTy)
import JetDiscovery.Run
import JetDiscovery.Types

data Group = Group
  { gKey :: Word64
  , gKind :: String
  , gSig :: String               -- ^ type signature
  , gPerInstance :: Integer      -- ^ milliWU static bound of one instance (largest seen)
  , gOccurrences :: Integer      -- ^ sum of multiplicities over the corpus
  , gPrograms :: [(String, Integer, Integer)]  -- ^ (program id, multiplicity, milliWU spent inside this sub-DAG)
  , gTotal :: Integer            -- ^ milliWU spent in this sub-DAG over the corpus
  , gMaxShare :: Double          -- ^ largest fraction of a single program's bound
  , gNodes :: Int
  }

-- | Group by exact hash (@False@) or by shape (@True@).
mine :: Bool -> [EntryResult] -> [Group]
mine byShape rs = sortBy (comparing (Down . gTotal)) (filter interesting (Map.elems groups))
 where
  key ni = if byShape then niShape ni else niHash ni
  rows = [ (key ni, (entryId (erEntry r), mCost (erMeasure r), ni))
         | r <- rs, ni <- mProfile (erMeasure r), niMult ni > 0, niTotal ni >= 1000 ]  -- >= 1 WU per instance
  groups = Map.fromListWith merge [ (k, single k pid root ni) | (k, (pid, root, ni)) <- rows ]
  single k pid root ni = Group
    { gKey = k, gKind = niKind ni, gSig = prettyTy (niSrc ni) ++ " -> " ++ prettyTy (niTgt ni)
    , gPerInstance = niTotal ni, gOccurrences = niMult ni
    , gPrograms = [(pid, niMult ni, niMult ni * niTotal ni)]
    , gTotal = niMult ni * niTotal ni
    , gMaxShare = fromInteger (niMult ni * niTotal ni) / fromInteger (max 1 root)
    , gNodes = niNodes ni }
  merge a b = a { gPerInstance = max (gPerInstance a) (gPerInstance b)
                , gOccurrences = gOccurrences a + gOccurrences b
                , gPrograms = mergeProgs (gPrograms a ++ gPrograms b)
                , gTotal = gTotal a + gTotal b
                , gMaxShare = max (gMaxShare a) (gMaxShare b) }
  mergeProgs ps = mapToTriples (Map.fromListWith (\(m1, t1) (m2, t2) -> (m1 + m2, t1 + t2)) [ (p, (m, t)) | (p, m, t) <- ps ])
  interesting g = take 4 (gKind g) /= "jet:" && (gOccurrences g >= 2 || length (gPrograms g) >= 2)

-- Map.toList returning triples
mapToTriples :: Map.Map String (Integer, Integer) -> [(String, Integer, Integer)]
mapToTriples m = [ (p, a, b) | (p, (a, b)) <- Map.toList m ]

wu :: Integer -> String
wu m = showFFloat (Just 3) (fromInteger m / 1000 :: Double) ""

groupsMarkdown :: Integer -> Int -> [Group] -> String
groupsMarkdown corpusTotal n gs = unlines $
  [ "| rank | sub-DAG id | root combinator | type signature | WU per instance | occurrences | programs | total WU | corpus share | max single-program share |"
  , "| ---: | --- | --- | --- | ---: | ---: | --- | ---: | ---: | ---: |" ] ++
  [ "| " ++ show i ++ " | `" ++ showHex (gKey g) "" ++ "` | " ++ gKind g ++ " | `" ++ clip 90 (gSig g) ++ "` | " ++ wu (gPerInstance g)
    ++ " | " ++ show (gOccurrences g) ++ " | " ++ intercalate ", " [ p ++ " ×" ++ show m | (p, m, _) <- gPrograms g ]
    ++ " | " ++ wu (gTotal g) ++ " | " ++ pctD (fromInteger (gTotal g) / fromInteger (max 1 corpusTotal)) ++ " | " ++ pctD (gMaxShare g) ++ " |"
  | (i, g) <- zip [1 :: Int ..] (take n gs) ]
 where
  clip k s = if length s > k then take (k - 1) s ++ "…" else s
  pctD x = showFFloat (Just 1) (100 * x) "%"

groupsTsv :: [Group] -> String
groupsTsv gs = unlines $
  intercalate "\t" ["id","kind","signature","per_instance_mwu","occurrences","programs","total_mwu","max_share"] :
  [ intercalate "\t" [ showHex (gKey g) "", gKind g, gSig g, show (gPerInstance g), show (gOccurrences g)
                     , intercalate ";" [ p ++ ":" ++ show m | (p, m, _) <- gPrograms g ], show (gTotal g), show (gMaxShare g) ]
  | g <- gs ]
