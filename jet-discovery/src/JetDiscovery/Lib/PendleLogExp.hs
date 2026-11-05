-- | Source-identical integer exp/ln on the narrower Pendle market domain.
-- Omit provably unreachable decompositions; use checked128-bit products where
-- the admitted range proves they fit, and retain full256-bit products otherwise.
module JetDiscovery.Lib.PendleLogExp where
import Prelude hiding (drop,take)
import qualified Prelude as H
import qualified Data.List as List
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import qualified Simplicity.Programs.Bit as B
import Simplicity.Programs.Generic (eq)
import Simplicity.Ty.Word
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S

guarded p body=(p&&&iden)>>>drop body
mulDiv128 a b d=L.divide (S.mul a b) d
expSeries :: Assert t => t Word128 Word128
expSeries=(iden&&&(iden&&&L.add (L.ks L.one20) iden))>>>step True 2>>>List.foldl' (>>>) iden [step False d|d<-[3..12]]>>>iih
 where
  step wide denominator=(iden&&&L.divide (if wide then L.mdiv ioh oh (L.ks L.one20) else mulDiv128 ioh oh (L.ks L.one20)) (L.ks denominator))>>>(take oh&&&(ih&&&L.add (take iih) ih))
expRef :: Assert t => t Word128 Word128
expRef=guarded (L.le iden (L.ks L.ones)>>>verify) ((S.mul iden (L.ks 100)&&&L.ks L.one20)>>>step x7 (L.ks a7)>>>step x8 (L.ks a8)>>>step x9 third>>>((ih&&&(oh>>>expSeries))>>>L.divide (L.mdiv oh ih (L.ks L.one20)) (L.ks 100)))
 where
  [(x7,a7),(x8,a8),(x9,a9)]=H.take 3 (H.drop 5 L.constants)
  step x product=L.select (L.le (L.ks x) oh) (L.sub oh (L.ks x)&&&product) iden
  -- For x<=ONE: x7 consumes the entire exponent; x8 can only follow no
  -- earlier product; x9 can follow only ONE20 or a8. Preserve exact floors.
  third=L.select ((ih&&&L.ks a8)>>>eq) (L.ks (a8*a9 `div`L.one20)) (L.ks a9)

odd20 :: Assert t => t Word128 Word128
odd20=(mulDiv128 iden iden (L.ks L.one20)&&&(iden&&&iden))>>>List.foldl' (>>>) iden [step d|d<-[3,5,7,9,11]]>>>iih
 where
  step denominator=(iden&&&mulDiv128 ioh oh (L.ks L.one20))>>>(take oh&&&(ih&&&L.add (take iih) (L.divide ih (L.ks denominator))))
lnPositive :: Assert t => t Word128 Word128
lnPositive=(S.mul iden (L.ks 100)&&&L.ks 0)>>>List.foldl' (>>>) iden (map step (H.drop 5 L.constants))>>>(ih&&&(oh>>>z>>>odd20))>>>L.divide (L.add oh (S.mul ih (L.ks 2))) (L.ks 100)
 where
  step (x,a)=L.select (L.le (L.ks a) oh) (L.mdiv oh (L.ks L.one20) (L.ks a)&&&L.add ih (L.ks x)) iden
  z=L.mdiv (L.sub iden (L.ks L.one20)) (L.ks L.one20) (L.add iden (L.ks L.one20))
ln18 :: Assert t => t Word128 L.Signed
ln18=(L.lt iden (L.ks L.ones)&&&iden)>>>(oh&&&(L.select oh (L.divide (L.ks L.one36) ih) ih>>>lnPositive))
ln36 :: Assert t => t Word128 L.Signed
ln36=(L.lt iden (L.ks L.ones)&&&S.mul iden (L.ks L.ones))>>>(oh&&&L.mdiv difference (L.ks L.one36) (L.add ih (L.ks L.one36)))>>>(oh&&&(ih>>>L.oddSeries L.one36 8>>>L.divide (S.mul iden (L.ks 2)) (L.ks L.ones)))
 where difference=L.select oh (L.sub (L.ks L.one36) ih) (L.sub ih (L.ks L.one36))
lnRef :: Assert t => t Word128 L.Signed
lnRef=guarded (B.and (L.le (L.ks (L.ones `div`3)) iden) (L.le iden (L.ks (3*L.ones)))>>>verify) (L.select L.near ln36 ln18)
