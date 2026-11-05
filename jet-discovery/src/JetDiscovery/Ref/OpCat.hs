-- | The byte-string relation in BIP347, independent of the typed word encoding.
module JetDiscovery.Ref.OpCat (cat, elementLimit) where

import qualified Data.ByteString as BS

elementLimit :: Int
elementLimit = 520

cat :: BS.ByteString -> BS.ByteString -> Maybe BS.ByteString
cat left right
  | BS.length left + BS.length right > elementLimit = Nothing
  | otherwise = Just (BS.append left right)
