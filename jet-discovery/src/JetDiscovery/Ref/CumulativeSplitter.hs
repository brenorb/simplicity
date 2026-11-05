-- | Independent Integer model of OpenZeppelin PaymentSplitter's Ether path.
module JetDiscovery.Ref.CumulativeSplitter
  ( Ledger(..), Action(..), receivedLimit, initial, apply, outstanding, encode ) where

import qualified Data.ByteString as BS
import Data.Serialize (putWord64be, runPut)

data Ledger = Ledger Integer (Integer,Integer,Integer) deriving (Eq,Show)
data Action = Receive Integer | Release Int deriving (Eq,Show)

receivedLimit :: Integer
receivedLimit = 2 ^ (48 :: Int) - 1

initial :: Ledger
initial = Ledger 0 (0,0,0)

outstanding :: Ledger -> Integer
outstanding (Ledger received (a,b,c)) = received - a - b - c

apply :: Ledger -> Action -> Maybe (Ledger,Maybe (Int,Integer))
apply (Ledger received (a,b,c)) action
  | received < 0 || received > receivedLimit = Nothing
  | not (and [0 <= r && r <= e | (r,e) <- zip paid entitlement]) = Nothing
  | otherwise = case action of
      Receive deposit
        | deposit > 0 && received + deposit <= receivedLimit ->
          Just (Ledger (received+deposit) (a,b,c),Nothing)
      Release i
        | i >= 0 && i < 3 && entitlement !! i > paid !! i ->
          let due = entitlement !! i - paid !! i
              [x,y,z] = [if j==i then entitlement !! j else r | (j,r)<-zip [0..] paid]
          in Just (Ledger received (x,y,z),Just (i,due))
      _ -> Nothing
 where
  paid = [a,b,c]
  entitlement = [received * share `div` 6 | share <- [1,2,3]]

encode :: Ledger -> BS.ByteString
encode (Ledger t (a,b,c)) = runPut (mapM_ (putWord64be . fromInteger) [t,a,b,c])
