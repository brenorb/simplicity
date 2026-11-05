{-# LANGUAGE ScopedTypeVariables #-}
-- | Exact two-outcome LMSR calcNetCost with the source's UpperBound paths,
-- EXP_LIMIT offset and signed truncation/positive-ceiling order. Only bounded
-- nonnegative inner exponents are admitted; caller owns the full claim ledger.
module JetDiscovery.Lib.LmsrCost where
import Prelude hiding (drop,take,not,and,or)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.Fixed192Bounded as F
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S

type Signed=(Bit,Word128) -- True means negative, with canonical nonnegative0.
type Amount=(Bit,Word64)
type Input=(Word64,((Word64,Word64),(Amount,Amount)))
type Output=Amount
select p a b=(p&&&iden)>>>cond a b
canonical :: Assert t => t Signed Signed
canonical=select ((ih&&&L.ks 0)>>>eq) (false&&&L.ks 0) iden
negative :: Assert t => t Signed Signed
negative=(not oh&&&ih)>>>canonical
sumSigned :: Assert t => t (Signed,Signed) Signed
sumSigned=select ((ooh&&&ioh)>>>eq) (ooh&&&L.add oih iih)
 (select (L.le oih iih) (ioh&&&L.sub iih oih) (ooh&&&L.sub oih iih))>>>canonical
minus a b=(a&&&(b>>>negative))>>>sumSigned
plus a b=(a&&&b)>>>sumSigned
signedLE :: Assert t => t (Signed,Signed) Bit
signedLE=select ooh (select ioh (L.le iih oih) true) (select ioh false (L.le oih iih))
maximumSigned a b=(a&&&b)>>>select signedLE ih oh
positiveMagnitude :: Assert t => t Signed Word128
positiveMagnitude=((oh>>>not iden>>>verify)&&&ih)>>>ih
funding :: Core t => t Input Word64
funding=oh
balanceA,balanceB :: Core t => t Input Word64
balanceA=drop (take oh)
balanceB=drop (take ih)
quantityA,quantityB :: Core t => t Input Amount
quantityA=drop (drop oh)
quantityB=drop (drop ih)
toSigned x=(x>>>oh)&&&L.u64 (x>>>ih)
unsigned x=false&&&L.u64 x
log2N,expLimit :: Integer
log2N=F.one+4 -- exact source binaryLog(2*ONE,UpperBound)
expLimit=3394200909562557497344

costRef :: Simplicity t => t Input Output
costRef=(bounds&&&iden)>>>drop ((iden&&&(numeratorA&&&numeratorB))>>>(take iden&&&(scale ioh&&&scale iih))>>>(iden&&&offset)>>>(iden&&&expSum)>>>signedCost>>>ceilCost)
 where
  bounds=checks [le64 (F.k64 1000) funding,le64 funding (F.k64 (10^6)),le64 balanceA cap,le64 balanceB cap,le64 (quantityA>>>ih) funding,le64 (quantityB>>>ih) funding]
  cap=S.mul (L.u64 funding) (L.ks 10)>>>S.narrow
  le64 a b=(a&&&b)>>>A.le word64>>>verify
  checks=foldr (\a b->(a&&&b)>>>unit) unit
  numeratorA=minus (toSigned quantityA) (unsigned balanceA)
  numeratorB=minus (toSigned quantityB) (unsigned balanceB)
  -- Domain=(Input,(signed numerA,signed numerB)); all source divisions of
  -- signed products truncate toward0, hence floor on the magnitude.
  scale value=(value>>>oh)&&&L.divide (S.mul (value>>>ih) (L.ks log2N)) (L.u64 (take funding))
  offset=minus (maximumSigned ioh iih) (false&&&L.ks expLimit)
  -- Domain=((Input,(scaledA,scaledB)),offset). Both exponents and their full
  -- sum are computed, never replaced by an offchain cost or floating point.
  exponent value=minus value ih>>>positiveMagnitude>>>F.pow2Upper
  expSum=F.add256 (exponent (take ioh)) (exponent (take iih))
  -- Domain=(((Input,(scaledA,scaledB)),offset),sum).
  signedCost=take (take (take funding))&&&plus (false&&&(ih>>>F.log2Upper)) (take ih)
  -- Domain=(funding,signed(log2(sum)+offset)). Preserve the two source
  -- operations before final ceiling: net*ONE/log2N, then *funding.
  intermediate=S.mul (L.mdiv iih (L.ks F.one) (L.ks log2N)) (L.u64 oh)
  ceilCost=(ioh&&&intermediate)>>>(oh&&&(select oh (L.divide ih (L.ks F.one)) (L.divide (L.add ih (L.ks (F.one-1))) (L.ks F.one))))>>>canonical>>>(oh&&&(ih>>>S.narrow))
costWrapped :: J.WrappedSimplicity Input Output
costWrapped=J.jetSubst costRef
{-# NOINLINE costWrapped #-}
cost :: Simplicity t => t Input Output
cost=J.unwrap costWrapped

costInteger :: Integer -> Integer -> Integer -> Integer -> Integer -> Integer
costInteger funding poolA poolB qa qb
 |funding<1000||funding>10^6||poolA<0||poolB<0||poolA>10*funding||poolB>10*funding||abs qa>funding||abs qb>funding=error "bounded LMSR input domain"
 |otherwise=if scaled<=0 then scaled `quot`F.one else (scaled+F.one-1) `quot`F.one
 where
  a=(qa-poolA)*log2N `quot`funding
  b=(qb-poolB)*log2N `quot`funding
  offset=max a b-expLimit
  expSum=F.pow2UpperInteger (a-offset)+F.pow2UpperInteger (b-offset)
  net=F.log2UpperInteger expSum+offset
  scaled=(net*F.one `quot`log2N)*funding
