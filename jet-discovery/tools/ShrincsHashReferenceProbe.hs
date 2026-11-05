module Main where
import Control.Monad (forM_,unless)
import qualified JetDiscovery.Ref.ShrincsHash as H
import qualified JetDiscovery.Ref.Shrincs as R
main :: IO ()
main=do
 forM_ H.seededCases $ \(seed,p@(layer,tree,domain,keypair,chain),start,node)->do
  let expected=foldl (\v j->R.tweak seed (R.adrs (fromInteger layer) tree (fromInteger domain) keypair chain (toInteger j)) v) node [start..14]
      actual=do mid<-H.seedStateSpec seed;prefix<-H.encodePrefix p;H.chainSpec mid prefix start node
      ok=actual==Just expected
  print ((p,start),ok)
  unless ok (error "compression reference disagrees with independent full-message SHA256")
