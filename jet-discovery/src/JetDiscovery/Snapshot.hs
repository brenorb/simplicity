{-# LANGUAGE GADTs #-}
-- | Reproducible checkpoints for long corpus runs. Only plain measurements
-- and profiles are retained, releasing the source interpreter's DAGs.
module JetDiscovery.Snapshot (sourceFingerprint, saveResult, loadResult) where

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.List (sort, isSuffixOf)
import Data.Word (Word64)
import Data.Serialize (decode)
import Text.Read (readMaybe)
import System.Environment (getExecutablePath)
import System.Directory (listDirectory, doesDirectoryExist, doesFileExist, createDirectoryIfMissing, renameFile)
import qualified Simplicity.Ty as T
import Simplicity.Ty (TyF(..))
import Simplicity.Digest (Hash256)
import JetDiscovery.Profile
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx (sha256, hashToBytes, hex, unhex)

data STy = U | W Integer | S STy STy | P STy STy deriving (Read, Show)
data SNode = SN Int Word64 String Word64 String STy STy Integer Integer Integer Int deriving (Read, Show)
data SMeasure = SM String [Integer] [SNode] [(String,Integer)] [(String,(Integer,Integer))] [(String,Integer)] deriving (Read, Show)
data Snapshot = Snapshot Int String String SMeasure [(String,Bool,Bool,String)] deriving (Read, Show)

toTy = snd . T.memoCataTy go
 where
  go One = (Nothing,U)
  go (Sum (Nothing,U) (Nothing,U)) = (Just 1,W 1)
  go (Sum (_,a) (_,b)) = (Nothing,S a b)
  go (Prod (Just n,_) (Just m,_)) | n==m = (Just (2*n),W (2*n))
  go (Prod (_,a) (_,b)) = (Nothing,P a b)
fromTy U = T.one
fromTy (W 1) = T.sum T.one T.one
fromTy (W n) | n>1 && even n = let t=fromTy (W (n `div` 2)) in T.prod t t
fromTy (W _) = error "invalid snapshot word type"
fromTy (S a b) = T.sum (fromTy a) (fromTy b)
fromTy (P a b) = T.prod (fromTy a) (fromTy b)
hashText = hex . hashToBytes
readHash s = case decode (unhex s) of Right h -> h; Left e -> error ("invalid snapshot hash: "++e)

packNode n = SN (niIndex n) (niHash n) (hashText (niCmr n)) (niShape n) (niKind n)
  (toTy (niSrc n)) (toTy (niTgt n)) (niSelf n) (niTotal n) (niMult n) (niNodes n)
unpackNode (SN i h c s k a b w t m n) = NodeInfo i h (readHash c) s k (fromTy a) (fromTy b) w t m n
packM m = SM (hashText (mCmr m))
  [mCost m,mCostBase m,mCostWhatIf m,toInteger (mProgBits m),toInteger (mWitBits m),toInteger (mNodes m),mProfileTotal m]
  (map packNode (mProfile m)) (mWhatIfJets m) (mCandidateCosts m) (mAblations m)
unpackM (SM c [w,b,f,p,v,n,t] ns js cs as) = Measurement (readHash c) w b f (fromInteger p) (fromInteger v) (fromInteger n) (map unpackNode ns) js cs t as
unpackM _ = error "invalid snapshot measurement schema"
pack fp r = Snapshot 2 fp (entryId (erEntry r)) (packM (erMeasure r))
  [(vrName v,vrExpect v==Accept,vrOk v,vrNote v) | v<-erVectors r]
unpack e (Snapshot _ _ _ m vs) = EntryResult e (unpackM m)
  [VectorResult n (if expected then Accept else Reject) ok note | (n,expected,ok,note)<-vs]

saveResult :: FilePath -> String -> EntryResult -> IO ()
saveResult dir fp r = do
  createDirectoryIfMissing True dir
  let path=dir++"/"++entryId (erEntry r)++".snapshot"
  writeFile (path++".tmp") (show (pack fp r)++"\n")
  renameFile (path++".tmp") path

loadResult :: FilePath -> String -> Entry -> IO (Maybe EntryResult)
loadResult dir fp e = do
  let path=dir++"/"++entryId e++".snapshot"
  exists<-doesFileExist path
  if not exists then return Nothing else do
    contents<-readFile path
    return $ case readMaybe contents of
      Just s@(Snapshot 2 stored ident _ vs) | stored==fp && ident==entryId e &&
        [(name,expected)|(name,expected,_,_)<-vs]==vectorHeaders e -> Just (unpack e s)
      _ -> Nothing
 where vectorHeaders (Entry _ _ _ _ _ _ _ vs)=[(vecName v,vecExpect v==Accept)|v<-vs]

-- Hash inputs, not generated reports or build products. Changing any local
-- source, vector/spec, in-tree Haskell/C source, or project build settings
-- invalidates all checkpoints. The fingerprint is independent of commits.
sourceFingerprint :: IO String
sourceFingerprint = do
  files<-concat <$> mapM walk ["src","app","vendor-specs","corpus/bips","../Haskell","../C",
                              "jet-discovery.cabal","cabal.project","../Simplicity.cabal"]
  exe<-getExecutablePath
  chunks<-mapM framed (sort files++[exe])
  return (hashText (sha256 (B.concat chunks)))
 where
  walk path = do
    dir<-doesDirectoryExist path
    if dir then do
      names<-listDirectory path
      concat <$> mapM (walk . ((path++"/")++)) (filter (`notElem` [".git","__pycache__","dist-newstyle"]) names)
    else do
      exists<-doesFileExist path
      return [path | exists && not (any (`isSuffixOf` path) [".o",".hi",".dyn_o",".dyn_hi",".DS_Store"])]
  framed path = do
    bytes<-B.readFile path
    return (C.pack (show (length path)++":"++path++show (B.length bytes)++":")<>bytes)
