-- | A transparent Fibonacci AIR with a multiplicative subgroup in CM31,
-- SHA-256 commitments, QM31 OOD/DEEP batching, and binary FRI. This is a
-- research protocol, not a Stwo wire-format implementation or a ZK proof.
module JetDiscovery.Ref.FibonacciStark where

import Prelude hiding (quot)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Bits (shiftR, testBit, (.&.))
import qualified Data.Vector as V
import Data.List (foldl')
import JetDiscovery.Corpus.Stark (HQ, p31, hQAdd, hQSub, hQMul)
import JetDiscovery.Ref.CircleFri (gen, qm31Bytes, alphaOf)
import JetDiscovery.Tx (sha256, hashToBytes)

type Q = HQ
zero, one :: Q
zero = ((0,0),(0,0))
one = base 1
base :: Integer -> Q
base a = ((a `mod` p31,0),(0,0))
add, sub, mul :: Q -> Q -> Q
add = hQAdd
sub = hQSub
mul = hQMul
pow :: Q -> Integer -> Q
pow _ 0 = one
pow a n | even n = let t = pow a (n `div` 2) in mul t t
        | otherwise = mul a (pow a (n-1))
inv :: Q -> Q
inv a | a == zero = error "inverse of zero"
      | otherwise = pow a (p31^ (4 :: Int)-2)
divide a b = mul a (inv b)
sha = hashToBytes . sha256

data Parameters = Parameters { traceLog :: Int, domainLog :: Int, queryCount :: Int }
  deriving (Eq, Show)
-- 1024 trace rows, 65536 LDE points, 48 transcript-derived query draws.
-- These are cryptographic-sized query and extension-field dimensions; no
-- formally proved security-bit claim is made for this custom implementation.
realistic = Parameters 10 16 48
small = Parameters 4 8 8
generator k = pow ((fst gen, snd gen),(0,0)) (2^(31-k))
coset = base 3
fib n = take n (go 1 1) where go a b = a : go b ((a+b) `mod` p31)
statement p = sha (C.pack ("JetDiscovery/FibonacciSTARK/v1/" ++ show p ++ "/1/1/" ++ show (last (fib (2^traceLog p)))))

-- Radix-two FFT. Operands are vectors rather than linked-list indexed tables.
fft :: Q -> V.Vector Q -> V.Vector Q
fft w xs
  | V.length xs == 1 = xs
  | otherwise = V.generate n $ \j -> let k=j `mod` h; t=mul (ws V.! k) (oddF V.! k)
                                     in (if j<h then add else sub) (evenF V.! k) t
 where
  n=V.length xs; h=n `div` 2
  evenF=fft (mul w w) (V.generate h (\j -> xs V.! (2*j)))
  oddF=fft (mul w w) (V.generate h (\j -> xs V.! (2*j+1)))
  ws=V.iterateN h (mul w) one
interpolate xs = V.map (`mul` inv (base (toInteger (V.length xs)))) (fft (inv (generator (ilog (V.length xs)))) xs)
ilog n = length (takeWhile (>1) (iterate (`div` 2) n))
evaluatePoly cs x = V.foldr (\a b -> add a (mul x b)) zero cs
lde k c cs = fft (generator k) (V.generate (2^k) (\j -> if j<V.length cs then mul (cs V.! j) (powers V.! j) else zero))
 where powers=V.iterateN (V.length cs) (mul c) one

-- Synthetic division (f(X)-f(z))/(X-z), coefficients in ascending order.
quot cs z = V.fromList (reverse (init (tail (scanl (\b a -> add a (mul z b)) zero (reverse (V.toList cs))))))
polyAdd a b = V.generate (max (V.length a) (V.length b)) (\j -> add (at a j) (at b j))
 where at v j = if j<V.length v then v V.! j else zero
scale s = V.map (mul s)

data Opening = Opening { values :: (Q,Q), siblings :: [B.ByteString] } deriving (Eq, Show)
data FriQuery = FriQuery { traceOpening :: Opening, compositionOpening :: Opening,
                          deepInverses :: [(Q,Q,Q)], friOpenings :: [Opening], friInverses :: [Q] }
  deriving (Eq, Show)
data Proof = Proof { traceRoot :: B.ByteString, compositionRoot :: B.ByteString,
                     ood :: [Q], airQuotients :: [Q], friRoots :: [B.ByteString],
                     finalValue :: Q, queries :: [FriQuery] } deriving (Eq, Show)
-- Merkle leaves are value hashes; the first parent commits an antipodal pair.
tree vs = V.fromList (takeWhile (not . V.null) (iterate up pairs))
 where
  h=V.length vs `div` 2
  pairs=V.generate h (\j -> sha (sha (qm31Bytes (vs V.! j)) <> sha (qm31Bytes (vs V.! (j+h)))))
  up xs | V.length xs==1 = V.empty
        | otherwise = V.generate (V.length xs `div` 2) (\j -> sha ((xs V.! (2*j)) <> (xs V.! (2*j+1))))
root tr=V.head (V.last tr)
opening vs tr q = Opening (vs V.! j, vs V.! (j+h))
  [ (tr V.! k) V.! ((j `shiftR` k) `xor1` ()) | k<-[0..V.length tr-2] ]
 where h=V.length vs `div` 2; j=q `mod` h
       xor1 x () = if odd x then x-1 else x+1
checkOpening k q r (Opening (a,b) path) = length path==k-1 &&
  foldl' (\nd (j,s) -> sha (if testBit q j then s<>nd else nd<>s))
    (sha (sha (qm31Bytes a) <> sha (qm31Bytes b))) (zip [0..] path)==r
canonical ((a,b),(c,d)) = all (\x -> x>=0 && x<p31) [a,b,c,d]

-- Transcript order: statement, T root, C root, all four OOD answers, then
-- every FRI root, then the final constant. Counters domain-separate queries.
challenges p pr = (a,z,rho,betas,seed)
 where
  ht=sha (statement p<>traceRoot pr); a=alphaOf ht
  hc=sha (ht<>compositionRoot pr); z=alphaOf hc
  ho=sha (hc<>B.concat (map qm31Bytes (ood pr)))
  rho=alphaOf ho
  hs=tail (scanl (\h r -> sha (h<>r)) ho (friRoots pr))
  betas=map alphaOf hs
  seed=sha (last hs<>qm31Bytes (finalValue pr))
word32 :: Int -> B.ByteString
word32 k=B.pack [fromIntegral (k `shiftR` (8*j))|j<-[3,2,1,0]]
scheduledIndices p seed = [ fromInteger (B.foldl' (\a b -> a*256+toInteger b) 0 (B.take 4 (sha (seed<>word32 k)))) .&. (2^(domainLog p-1)-1) | k<-[0..queryCount p-1] ]

prove :: Parameters -> Proof
prove p = result
 where
  n=2^traceLog p; k=domainLog p; g=generator (traceLog p)
  t=interpolate (V.fromList (map base (fib n)))
  tv=lde k coset t; tt=tree tv; tr=root tt
  ht=sha (statement p<>tr); alpha=alphaOf ht
  -- Transition numerator has degree n-1 and is divisible by Z_trans of
  -- degree n-2, so the transition quotient has degree at most one.
  numerator=V.imap (\j c -> mul c (sub (sub (pow g (2*toInteger j)) (pow g (toInteger j))) one)) t
  r1=inv g; r2=mul r1 r1
  -- Z_trans=(X^n-1)/((X-r1)(X-r2)); its leading two coefficients are 1,r1+r2.
  q1=numerator V.! (n-1)
  q0=sub (numerator V.! (n-2)) (mul q1 (add r1 r2))
  qt=V.fromList [q0,q1]
  pieces=[qt,quot t one,quot t g,quot t (pow g (toInteger (n-1)))]
  cp=foldl1 polyAdd (zipWith scale (iterate (mul alpha) one) pieces)
  cv=lde k coset cp; ct=tree cv; cr=root ct
  z=alphaOf (sha (ht<>cr))
  zs=[z,mul g z,mul (mul g g) z]
  tz=map (evaluatePoly t) zs
  cz=evaluatePoly cp z
  os=tz++[cz]
  aq=zipWith evaluatePoly pieces (repeat z)
  ho=sha (sha (ht<>cr)<>B.concat (map qm31Bytes os)); rho=alphaOf ho
  dp=foldl1 polyAdd (zipWith scale (iterate (mul rho) one) (map (quot t) zs++[quot cp z]))
  -- Build FRI with challenges taken after each committed layer.
  layers=go 0 ho coset dp
  go l h c coeff
    | l==traceLog p = []
    | otherwise = let vs=lde (k-l) c coeff; mt=tree vs; r=root mt
                      hh=sha (h<>r); beta=alphaOf hh
                      next=V.generate ((V.length coeff+1) `div` 2) (\j -> add (coeff V.! (2*j)) (if 2*j+1<V.length coeff then mul beta (coeff V.! (2*j+1)) else zero))
                  in (vs,mt,r,hh,next):go (l+1) hh (mul c c) next
  roots=[r|(_,_,r,_,_)<-layers]
  f=V.head (fifth (last layers)); fifth (_,_,_,_,v)=v
  seed=sha (fourth (last layers)<>qm31Bytes f); fourth (_,_,_,h,_)=h
  idx=scheduledIndices p seed
  mkQuery q = FriQuery (opening tv tt q) (opening cv ct q)
    [let x=mul coset (pow (generator k) (toInteger (q+s*2^(k-1)))) in (inv (sub x z),inv (sub x (zs!!1)),inv (sub x (zs!!2))) | s<-[0,1]]
    [opening vs mt q | (vs,mt,_,_,_)<-layers]
    [inv (mul (pow coset (2^l)) (pow (generator (k-l)) (toInteger (q `mod` (2^(k-l-1)))))) | l<-[0..traceLog p-1]]
  result=Proof tr cr os aq roots f (map mkQuery idx)

-- The Haskell carrier is more permissive than the fixed-width witness wire
-- schema. Validate it before indexing or narrowing to Simplicity words.
wellShaped :: Parameters -> Proof -> Bool
wellShaped p pr = traceLog p>=2 && traceLog p<=16 && domainLog p>traceLog p && domainLog p<=30 && queryCount p>0 &&
  length (ood pr)==4 && length (airQuotients pr)==4 && length (friRoots pr)==traceLog p && length (queries pr)==queryCount p &&
  all ((==32) . B.length) ([traceRoot pr,compositionRoot pr]++friRoots pr) && all shape (queries pr)
 where
  op k x = length (siblings x)==k-1 && all ((==32) . B.length) (siblings x)
  shape q = op (domainLog p) (traceOpening q) && op (domainLog p) (compositionOpening q) &&
    length (deepInverses q)==2 && length (friOpenings q)==traceLog p && length (friInverses q)==traceLog p &&
    and (zipWith op [domainLog p,domainLog p-1..] (friOpenings q))

wireValues :: Proof -> [Q]
wireValues pr = ood pr++airQuotients pr++[finalValue pr]++concatMap queryValues (queries pr)
 where
  pair op=let (a,b)=values op in [a,b]
  queryValues q = pair (traceOpening q)++pair (compositionOpening q)++concatMap pair (friOpenings q)++friInverses q++concatMap (\(a,b,c)->[a,b,c]) (deepInverses q)
wireEncodable :: Parameters -> Proof -> Bool
wireEncodable p pr = wellShaped p pr && all word32Q (wireValues pr)
 where word32Q ((a,b),(c,d))=all (\v->v>=0 && v<2^(32::Int)) [a,b,c,d]

verify :: Parameters -> Proof -> Bool
verify p pr
  | not (wellShaped p pr) = False
  | otherwise = all canonical (ood pr++airQuotients pr++[finalValue pr]) && snd z/=(0,0) && airOk && and (zipWith check idx (queries pr))
 where
  (a,z,rho,bs,seed)=challenges p pr; idx=scheduledIndices p seed
  [tz,tgz,tggz,cz]=ood pr; [qt,q0,q1,ql]=airQuotients pr
  n=2^traceLog p; k=domainLog p; g=generator (traceLog p); gi=inv g
  zp=sub (pow z (toInteger n)) one
  airOk=mul (sub (sub tggz tgz) tz) (mul (sub z gi) (sub z (mul gi gi)))==mul qt zp &&
    mul q0 (sub z one)==sub tz one && mul q1 (sub z g)==sub tz one &&
    mul ql (sub z (pow gi 1))==sub tz (base (last (fib n))) &&
    cz==foldl1 add (zipWith mul (iterate (mul a) one) [qt,q0,q1,ql])
  deep x t c (i,j,h) = foldl1 add (zipWith mul (iterate (mul rho) one)
    [mul (sub t tz) i,mul (sub t tgz) j,mul (sub t tggz) h,mul (sub c cz) i])
  check q qp = length (friOpenings qp)==traceLog p && length (friInverses qp)==traceLog p && length (deepInverses qp)==2 &&
    checkOpening k q (traceRoot pr) (traceOpening qp) && checkOpening k q (compositionRoot pr) (compositionOpening qp) &&
    and [let x=mul coset (pow (generator k) (toInteger (q+s*2^(k-1))))
             t=side s (values (traceOpening qp)); c=side s (values (compositionOpening qp)); is@(i,j,h)=deepInverses qp!!s
             ds=[sub x z,sub x (mul g z),sub x (mul (mul g g) z)]
         in all canonical [t,c,i,j,h] && and (zipWith (\d v -> mul d v==one) ds [i,j,h]) && deep x t c is==side s (values (head (friOpenings qp))) | s<-[0,1]] &&
    and [let op=friOpenings qp!!l; (v,w)=values op; xi=friInverses qp!!l
             x=mul (pow coset (2^l)) (pow (generator (k-l)) (toInteger (q `mod` (2^(k-l-1)))))
             folded=mul (base ((p31+1) `div` 2)) (add (add v w) (mul (bs!!l) (mul (sub v w) xi)))
             next=if l==traceLog p-1 then finalValue pr else side (if testBit q (k-l-2) then 1 else 0) (values (friOpenings qp!!(l+1)))
         in all canonical [v,w,xi] && checkOpening (k-l) q (friRoots pr!!l) op && mul x xi==one && folded==next | l<-[0..traceLog p-1]]
  side 0=fst; side _=snd
