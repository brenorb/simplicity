-- | Integer reference for the complete KoalaBear16 Poseidon2 permutation.
-- False selects the published Plonky3 default KAT profile; True selects the
-- exact Ziren constants consumed by GOAT's pinned Bitcoin verifier dependency.
module JetDiscovery.Ref.Poseidon2
 (q,diagonal,external,permutation,katInput,katExpected,selfCheck,cases) where
import qualified Data.List as L
import JetDiscovery.Ref.Poseidon2Constants
q :: Integer
q=2130706433
pow _ 0=1
pow a e | even e=let h=pow a(e`div`2)in h*h`mod`q
        | otherwise=a*pow a(e-1)`mod`q
inv2 e=pow(2^e)(q-2)
diagonal :: [Integer]
diagonal=map(`mod`q)[-2,1,2,inv2 1,3,4,negate(inv2 1),-3,-4,inv2 8,inv2 3,inv2 24,negate(inv2 8),negate(inv2 3),negate(inv2 4),negate(inv2 24)]
-- Dense Integer matrix is intentionally independent of optimized term wiring.
external :: [Integer] -> [Integer]
external xs=[(y!!i+sum[y!!j|j<-[i`mod`4,i`mod`4+4..15]])`mod`q|i<-[0..15]]
 where
  matrix=[[2,3,1,1],[1,2,3,1],[1,1,2,3],[3,1,1,2]]
  block b=[sum(zipWith(*)row b)`mod`q|row<-matrix]
  y=concat[block(take 4(drop i xs))|i<-[0,4,8,12]]
permutation :: Bool -> [Integer] -> Maybe [Integer]
permutation profile xs
 | length xs/=16 || any(\x->x<0 || x>=q)xs=Nothing
 | otherwise=Just(L.foldl' full afterPartial final)
 where
  initial=if profile then zirenInitial else defaultInitial
  middle=if profile then zirenInternal else defaultInternal
  final=if profile then zirenFinal else defaultFinal
  cube x=x*x`mod`q*x`mod`q
  full a constants=external(map cube(zipWith(\x c->(x+c)`mod`q)a constants))
  partial a c=let changed=cube((head a+c)`mod`q):tail a;s=sum changed
               in zipWith(\d x->(s+d*x)`mod`q)diagonal changed
  afterInitial=L.foldl' full(external xs)initial
  afterPartial=L.foldl' partial afterInitial middle
selfCheck :: Bool
selfCheck=permutation False katInput==Just katExpected
 && permutation False(replicate 15 0)==Nothing
 && permutation False(q:replicate 15 0)==Nothing
cases :: [(Bool,[Integer])]
cases=[(False,katInput)]++[(profile,x)|profile<-[False,True],x<-[replicate 16 0,replicate 16 1,replicate 16(q-1),[0..15],[((i+3)^7)`mod`q|i<-[0..15]]]]
