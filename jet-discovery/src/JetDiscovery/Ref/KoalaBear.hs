-- | Independent Integer model of the candidate's total32-bit word relation.
module JetDiscovery.Ref.KoalaBear (addWordSpec,q) where
q :: Integer
q=2130706433
addWordSpec :: Integer -> Integer -> Integer
addWordSpec a b=if u<q then u else u-q
 where u=(a+b)`mod`(2^(32::Int))
